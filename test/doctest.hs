{-# LANGUAGE CPP #-}

import Test.DocTest
import Prelude (IO)

main :: IO ()
main = doctest 
  [ "-isrc" 
  , "src/Data/Connection.hs"
  , "src/Data/Connection/Conn.hs"
  , "src/Data/Connection/Class.hs"
  , "src/Data/Connection/Float.hs"
  ]
