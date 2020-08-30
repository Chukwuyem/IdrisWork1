
module RBTree2

data Colour = Red | Black

data RBTree : Nat -> Type -> Type where
      Empty : Ord elem => RBTree Z elem
      Node : Ord elem => (left: RBTree n elem) -> (val: elem) -> (col: Colour) -> (right: RBTree n elem) -> RBTree (S n) elem

{- this implementation includes the black height of the node, with empty node having black height 0 -}
