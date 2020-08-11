
import RBTree

listToTree : Ord a => List a -> RBTree a
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs)
