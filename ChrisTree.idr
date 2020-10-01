-- Black node can have red or black child nodes.
-- Red node can only have black child nodes.

data Colour = Red | Black

total
mergeColours : Colour -> Colour -> Colour -> Colour
mergeColours Black Black Red = Red
mergeColours _ _ _ = Black

data RBTree : Type -> Nat -> Colour -> Type where
  RBNil : RBTree a 0 Black
  RBBlack : a -> RBTree a h c1 -> RBTree a h c2 -> RBTree a (S h) Black
  RBRed : a -> RBTree a h Black -> RBTree a h Black -> RBTree a h Red

-- data RBUnbalanced : Type -> Nat -> Colour -> Type where
--   RBLeftHeavy : a -> RBTree a h Red -> RBTree a h Black -> RBUnbalanced a h Red
--   RBRightHeavy : a -> RBTree a h Black -> RBTree a h Red -> RBUnbalanced a h Red
--   RBUnbalancedRed : a -> RBTree a h c1 -> RBTree a h c2 -> RBTree a h Red

-- These are shorthand for leaf nodes, where both children are nil. Note the
-- black-heights are different because they *include* the top/root node.

redLeaf : a -> RBTree a 0 Red
redLeaf a = RBRed a RBNil RBNil

blackLeaf : a -> RBTree a 1 Black
blackLeaf a = RBBlack a RBNil RBNil

-- The following definitions assemble the tree pictured at
-- https://upload.wikimedia.org/wikipedia/commons/thumb/6/66/Red-black_tree_example.svg/1920px-Red-black_tree_example.svg.png

example1 : RBTree Int 1 Black
example1 =
  RBBlack 1 RBNil (redLeaf 6)

example8 : RBTree Int 1 Red
example8 =
  RBRed 8 example1 (blackLeaf 11)

example25 : RBTree Int 1 Black
example25 =
  RBBlack 25 (redLeaf 22) (redLeaf 27)

example17 : RBTree Int 1 Red
example17 =
  RBRed 17 (blackLeaf 15) example25

example13 : RBTree Int 2 Black
example13 =
  RBBlack 13 example8 example17

-- But we can't have two consecutive reds (this should throw type mismatch):
-- λ> RBRed 'A' (redLeaf 'B') RBNil

-- And we can't imbalance black:
-- λ> RBBlack 'A' (RBBlack 'B' (blackLeaf 'C') RBNil) RBNil

balance : RBTree e h a
  -> e -> RBTree e h b
  -> e -> RBTree e h c
  -> e -> RBTree e h d
  -> RBTree e (S h) Red

balance a x b y c z d =
  RBRed y (RBBlack x a b) (RBBlack z c d)

-- It's always possible to make the root of a tree black, but it might increase
-- the height.

incrementIfRed : Colour -> Nat -> Nat
incrementIfRed Red n = S n
incrementIfRed Black n = n

total
makeBlack : RBTree e h c -> RBTree e (incrementIfRed c h) Black
makeBlack (RBRed e l r) = RBBlack e l r
makeBlack (RBBlack e l r) = RBBlack e l r
makeBlack RBNil = RBNil

total
contains : Ord e => RBTree e h c -> e -> Bool
contains RBNil _ = False
contains (RBRed e l r) goal =
  case compare goal e of
    EQ => True
    LT => contains l goal
    GT => contains r goal
contains (RBBlack e l r) goal = -- Would be nice to elim this duplication
  case compare goal e of        -- but solve insert w/rebalancing first.
    EQ => True
    LT => contains l goal
    GT => contains r goal


-- What are all the types that can happen with bottom layer of insert?

-- At the root, tree will always be black. So we can insert a red and
-- bubble/rotate as much as needed (possibly all the way to root) without
-- changing the height. Then when all done, makeBlack will potentially increment
-- the height.

total
insert1 : Ord e => RBTree e 0 Black -> e -> RBTree e 0 Red
insert1 RBNil e = redLeaf e


--total
--insert2 : Ord e => RBTree e 1 Black -> e -> RBTree e 1 Black
--insert2 t@(RBBlack x _ _) | x == e = t
-- insert2 (RBBlack x RBNil RBNil) e =
--   case compare e x of
--     EQ => blackLeaf x
--     LT => RBBlack x (redLeaf e) RBNil
--     GT => RBBlack x RBNil (redLeaf e)

-- insert (RBRed x RBNil RBNil) e = -- 1R -> 2B
--   case compare e x of
--     EQ => blackLeaf x
--     LT => RBBlack x (redLeaf e) RBNil
--     GT => RBBlack x RBNil (redLeaf e)

-- insert (RBBlack x RBNil RBNil) e = -- 2B -> 2B
--   case compare e x of
--     EQ => blackLeaf x
--     LT => RBBlack x (redLeaf e) RBNil
--     GT => RBBlack x RBNil (redLeaf e)

-- insert t@(RBBlack x (RBRed w RBNil RBNil) RBNil) e = -- 2B -> 2B
--   case compare e x of
--     EQ => t
--     GT => RBBlack x (redLeaf w) (redLeaf x)
--     LT =>
--       case compare e w of
--         EQ => t
--         LT => RBBlack w (redLeaf e) (redLeaf x) -- e,w,x
--         GT => RBBlack e (redLeaf w) (redLeaf x) -- w,e,x



--
--  redLeaf 'X' : 1R
--    => RBBlack 'X' (redLeaf 'W') RBNil : 2B  // LT
--     | blackLeaf 'X' : 2B                    // EQ
--
--  blackLeaf 'X' : 2B
--    => RBBlack 'X' (redLeaf 'W') RBNil : 2B  // LT

-- insert : Ord e => RBTree e h c -> e -> RBTree e h Red
-- insert RBNil e = redLeaf e
-- insert (RBBlack x RBNil RBNil) e =
--   case compare e x of
--     EQ => (RBBlack x RBNil RBNil)
