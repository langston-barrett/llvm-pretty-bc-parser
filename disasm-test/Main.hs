{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Data.LLVM.BitCode (parseBitCodeLazyFromFile,Error(..),formatError)
import Text.LLVM.PP (ppLLVM,ppModule)

import Control.Monad (when)
import Data.Char (ord,isSpace,chr)
import Data.Monoid ( mconcat, Endo(..) )
import Data.Typeable (Typeable)
import System.Console.GetOpt
           ( ArgOrder(..), ArgDescr(..), OptDescr(..), getOpt, usageInfo )
import System.Directory (getTemporaryDirectory,removeFile)
import System.Environment (getArgs,getProgName)
import System.Exit (exitFailure,exitSuccess,ExitCode(..))
import System.FilePath ((<.>),dropExtension,takeFileName)
import System.IO
    (openBinaryTempFile,hClose,openTempFile,hPrint)
import System.Process
    (proc,createProcess,waitForProcess,cmdspec,CmdSpec(..),CreateProcess())
import qualified Control.Exception as X
import qualified Data.ByteString.Lazy as L


-- Option Parsing --------------------------------------------------------------

data Options = Options { optTests   :: [FilePath] -- ^ Tests
                       , optLlvmAs  :: String     -- ^ llvm-as  name
                       , optLlvmDis :: String     -- ^ llvm-dis name
                       , optHelp    :: Bool
                       } deriving (Show)

defaultOptions :: Options
defaultOptions  = Options { optTests   = []
                          , optLlvmAs  = "llvm-as"
                          , optLlvmDis = "llvm-dis"
                          , optHelp    = False
                          }

options :: [OptDescr (Endo Options)]
options  =
  [ Option "" ["with-llvm-as"] (ReqArg setLlvmAs "FILEPATH")
    "path to llvm-as"
  , Option "" ["with-llvm-dis"] (ReqArg setLlvmDis "FILEPATH")
    "path to llvm-dis"
  , Option "h" ["help"] (NoArg setHelp)
    "display this message"
  ]

setLlvmAs :: String -> Endo Options
setLlvmAs str = Endo (\opt -> opt { optLlvmAs = str })

setLlvmDis :: String -> Endo Options
setLlvmDis str = Endo (\opt -> opt { optLlvmDis = str })

setHelp :: Endo Options
setHelp  = Endo (\opt -> opt { optHelp = True })

addTest :: String -> Endo Options
addTest test = Endo (\opt -> opt { optTests = test : optTests opt })

getOptions :: IO Options
getOptions  =
  do args <- getArgs
     case getOpt (ReturnInOrder addTest) options args of

       (fs,[],[]) -> do let opts = appEndo (mconcat fs) defaultOptions

                        when (optHelp opts) $ do printUsage []
                                                 exitSuccess

                        return opts

       (_,_,errs) -> do printUsage errs
                        exitFailure

printUsage :: [String] -> IO ()
printUsage errs =
  do prog <- getProgName
     let banner = "Usage: " ++ prog ++ " [OPTIONS] test1.ll .. testn.ll"
     putStrLn (usageInfo (unlines (errs ++ [banner])) options)


-- Test Running ----------------------------------------------------------------

-- | Run all provided tests.
main :: IO ()
main  = do
  opts <- getOptions
  mapM_ (runTest opts) (optTests opts)

-- | A test failure.
data TestFailure
  = ParseError Error           -- ^ A parser failure.
    deriving (Typeable,Show)

instance X.Exception TestFailure

-- | Attempt to compare the assembly generated by llvm-pretty and llvm-dis.
runTest :: Options -> FilePath -> IO ()
runTest opts file = do
  putStr (showString file ":")
  X.handle logError                                  $
    X.handle logCommandError                         $
    X.bracket (generateBitCode  opts pfx file) removeFile $ \ bc     ->
    X.bracket (normalizeBitCode opts pfx bc)   removeFile $ \ norm   ->
    X.bracket (processBitCode        pfx bc)   removeFile $ \ parsed -> do
      ignore (wait (proc "diff" ["-u",norm,parsed]))
      putStrLn "success"
  where
  pfx = dropExtension (takeFileName file)

  logError (ParseError msg) = do
    putStrLn "failure"
    putStrLn (unlines (map ("; " ++) (lines (formatError msg))))

  logCommandError (CommandFailed cmd) = do
    putStrLn "failure"
    putStrLn ("Command ``" ++ cmd ++ "'' failed\n\n")

-- | Assemble some llvm assembly, producing a bitcode file in /tmp.
generateBitCode :: Options -> FilePath -> FilePath -> IO FilePath
generateBitCode Options { .. } pfx file = do
  tmp    <- getTemporaryDirectory
  (bc,h) <- openBinaryTempFile tmp (pfx <.> "bc")
  hClose h
  wait (proc optLlvmAs ["-o", bc, file])
  return bc

-- | Use llvm-dis to parse a bitcode file, to obtain a normalized version of the
-- llvm assembly.
normalizeBitCode :: Options -> FilePath -> FilePath -> IO FilePath
normalizeBitCode Options { .. } pfx file = do
  tmp      <- getTemporaryDirectory
  (norm,h) <- openTempFile tmp (pfx <.> "ll")
  hClose h
  wait (proc optLlvmDis ["-o", norm, file])
  stripComments norm
  return norm

-- | Parse a bitcode file using llvm-pretty, failing the test if the parser
-- fails.
processBitCode :: FilePath -> FilePath -> IO FilePath
processBitCode pfx file = do
  parseBitCodeLazyFromFile file >>=
    \case
      Left err -> X.throwIO (ParseError err)
      Right m  -> do
        tmp        <- getTemporaryDirectory
        (parsed,h) <- openTempFile tmp (pfx <.> "ll")
        hPrint h (ppLLVM (ppModule m))
        hClose h
        stripComments parsed
        return parsed

-- | Remove comments from a .ll file, stripping everything including the
-- semi-colon.
stripComments :: FilePath -> IO ()
stripComments path = do
  bytes <- L.readFile path
  removeFile path
  mapM_ (writeLine . dropComments) (bsLines bytes)
  where
  writeLine bs | L.null bs = return ()
               | otherwise = do
                 L.appendFile path bs
                 L.appendFile path (L.singleton 0x0a)

-- | Split a bytestring by its lines.
bsLines :: L.ByteString -> [L.ByteString]
bsLines = L.split char
  where
  char = fromIntegral (ord '\n')

-- | Take characters until the llvm comment delimiter is found.
dropComments :: L.ByteString -> L.ByteString
dropComments  = dropTrailingSpace . L.takeWhile (/= char)
  where
  char = fromIntegral (ord ';')

-- | Drop trailing space from a bytestring.
dropTrailingSpace :: L.ByteString -> L.ByteString
dropTrailingSpace bs
  | len <= 0  = L.empty
  | otherwise = L.take (loop len) bs
  where
  len = L.length bs - 1
  loop n | isSpace (chr (fromIntegral (L.index bs n))) = loop (n-1)
         | otherwise                                   = n

-- | A shell-command failure.
data CommandError
  = CommandFailed String -- ^ The command failed when running.
    deriving (Typeable,Show)

instance X.Exception CommandError

-- | Construct a command error, given a description of the command that was run.
commandError :: CmdSpec -> CommandError
commandError (ShellCommand str)  = CommandFailed str
commandError (RawCommand p args) = CommandFailed (unwords (takeFileName p:args))

-- | Run a command, waiting for it to return.
wait :: CreateProcess -> IO ()
wait cmd = do
  (_,_,_,ph) <- createProcess cmd
  status     <- waitForProcess ph
  case status of
    ExitFailure{} -> X.throwIO (commandError (cmdspec cmd))
    _             -> return ()

-- | Ignore a command that fails.
ignore :: IO () -> IO ()
ignore  = X.handle f
  where
  f :: CommandError -> IO ()
  f _ = return ()
