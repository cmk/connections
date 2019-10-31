import Control.Monad
import System.Exit (exitFailure)
import System.IO (BufferMode(..), hSetBuffering, stdout, stderr)


import qualified Test.Data.Float as F
import qualified Test.Data.Dioid.Signed as S
import qualified Test.Data.Connection.Int as CI
import qualified Test.Data.Connection.Word as CW


tests :: IO [Bool]
tests = sequence [S.tests] -- [CI.tests, CW.tests, F.tests] 

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering

  results <- tests

  unless (and results) exitFailure
