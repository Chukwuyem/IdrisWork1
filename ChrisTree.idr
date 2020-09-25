-- Black node can have red or black child nodes.
-- Red node can only have black child nodes.

data Colour = Red | Black

data RBTree : Type -> Nat -> Colour -> Type where
  RBNil : RBTree a 1 Black
  RBBlack : a -> RBTree a h c1 -> RBTree a h c2 -> RBTree a (S h) Black
  RBRed : a -> RBTree a h Black -> RBTree a h Black -> RBTree a h Red

-- These are shorthand for leaf nodes, where both children are nil. Note the
-- black-heights are different because they *include* the top/root node.

redLeaf : a -> RBTree a 1 Red
redLeaf a = RBRed a RBNil RBNil

blackLeaf : a -> RBTree a 2 Black
blackLeaf a = RBBlack a RBNil RBNil

-- The following definitions assemble the tree pictured at
-- https://upload.wikimedia.org/wikipedia/commons/thumb/6/66/Red-black_tree_example.svg/1920px-Red-black_tree_example.svg.png

example1 : RBTree Int 2 Black
example1 =
  RBBlack 1 RBNil (redLeaf 6)

example8 : RBTree Int 2 Red
example8 =
  RBRed 8 example1 (blackLeaf 11)

example25 : RBTree Int 2 Black
example25 =
  RBBlack 25 (redLeaf 22) (redLeaf 27)

example17 : RBTree Int 2 Red
example17 =
  RBRed 17 (blackLeaf 15) example25

example13 : RBTree Int 3 Black
example13 =
  RBBlack 13 example8 example17

-- But we can't have two consecutive reds (this should throw type mismatch):
-- λ> RBRed 'A' (redLeaf 'B') RBNil

-- And we can't imbalance black:
-- λ> RBBlack 'A' (RBBlack 'B' (blackLeaf 'C') RBNil) RBNil
