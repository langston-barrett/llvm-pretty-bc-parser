module Data.LLVM.BitCode (
    -- * Bitcode Parsing
    parseBitCode,     parseBitCodeFromFile
  , parseBitCodeLazy, parseBitCodeLazyFromFile

    -- * Re-exported
  , Error(..), formatError
  ) where

import Data.LLVM.BitCode.Bitstream
    (Bitstream,parseBitCodeBitstream,parseBitCodeBitstreamLazy)
import Data.LLVM.BitCode.IR (parseModule)
import Data.LLVM.BitCode.Parse (runParse,badRefError,Error(..))
import Data.LLVM.BitCode.PP (formatError)
import Text.LLVM.AST (Module)

import           Control.Monad ((<=<))
import qualified Control.Exception as X
import qualified Data.ByteString as S
import qualified Data.ByteString.Lazy as L
import           System.Exit (exitFailure)

import Debug.Trace

-- | Fail with an error message if the bitstream couldn't be parsed
handleBitstreamError :: Either String Bitstream -> IO Bitstream
handleBitstreamError e = trace "handleBitstreamError" $ do
  case e of
    Left err -> trace "handleBistreamError:Left" $ do
      putStrLn $ unlines [ "Error while parsing container format:"
                         , err
                         ]
      exitFailure
    Right bs -> trace "handleBistreamError:Right" $  pure bs

parseBitCode :: S.ByteString -> IO (Either Error Module)
parseBitCode = trace "parseBitstream" $
  parseBitstream <=< (handleBitstreamError . parseBitCodeBitstream)

parseBitCodeFromFile :: FilePath -> IO (Either Error Module)
parseBitCodeFromFile  =  trace "parseBitCodeFromFile" $ parseBitCode <=< S.readFile

parseBitCodeLazy :: L.ByteString -> IO (Either Error Module)
parseBitCodeLazy  = trace "parseBitCodeLazy" $
  parseBitstream <=< (handleBitstreamError . parseBitCodeBitstreamLazy)

parseBitCodeLazyFromFile :: FilePath -> IO (Either Error Module)
parseBitCodeLazyFromFile  = parseBitCodeLazy <=< L.readFile

parseBitstream :: Bitstream -> IO (Either Error Module)
parseBitstream bs = trace "parseBitstream" $
  X.handle (return . Left . badRefError)
           (X.evaluate (runParse (parseModule bs)))
