module Cmp where

import qualified P4F
import qualified TestP4FM

cmp = do
  a <- P4F.test2 P4F.expId4
  b <- TestP4FM.test TestP4FM.expId4
  print "P4F"
  putStrLn a
  writeFile "cmp.p4f" $ a
  writeFile "cmp.p4fm" $ b
  print "P4FM"
  putStrLn b
  print (a == b)
