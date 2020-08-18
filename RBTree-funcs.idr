
import RBTree

listToRBTree : Ord a => List a -> RBTree a
listToRBTree [] = Empty
listToRBTree (x :: xs) = insert x (listToRBTree xs)


-- search after an insert
srchInsCheck : Ord elem => elem -> RBTree elem -> Bool
srchInsCheck x Empty = False
srchInsCheck x s = rbSearch x (insert x s)

srchInsCheckL : Ord elem => elem -> List elem -> Bool
srchInsCheckL x [] = False
srchInsCheckL x xs = rbSearch x (insert x (listToRBTree xs))

{- the above two functions will return true because the insert and search functions
are correctly written. one way to make it fail is to miswrite either the search or the
insert function.. so in the case compare.. make LT go right and GT go left.. -}


-- check if a red node has a red child node
dubRedChildCheck : RBTree elem -> Bool
dubRedChildCheck Empty = False
dubRedChildCheck (Node (Node a x Red b) val Red right) = True
dubRedChildCheck (Node left val Red (Node a x Red b)) = True
dubRedChildCheck (Node left val col right) = False


-- rbSrchOpt : Ord elem => elem -> RBTree elem -> Bool
-- rbSrchOpt x rbnode =
--       let cand = Empty
