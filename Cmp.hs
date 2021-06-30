import qualified P4F
import qualified TestP4FM

cmp = do
  a <- P4F.test2 P4F.expId4
  b <- TestP4FM.test TestP4FM.expId4
  print (a == b)
  print "P4F"
  putStrLn a
  print "P4FM"
  putStrLn b

