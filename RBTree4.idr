
module RBTree4

data Colour = Red | Black

eq_color : Colour -> Colour -> Bool
eq_color Red Red = True
eq_color Black Black = True
eq_color _ _ = False

Eq (Colour) where
  (==) = eq_color

getHght : Colour -> Nat -> Colour -> Nat -> Nat
getHght Black x Black y = (S x)
getHght Red x Red y = x
getHght Red x Black y = x
getHght Black x Red y = y

data RBTree : Nat -> Colour -> Type -> Type where
      Empty : Ord elem => RBTree Z Black elem
      Node : Ord elem => (left: RBTree p x elem) -> (val: elem) -> (col: Colour) ->
                        (h: Nat) -> (right: RBTree q y elem) -> RBTree (getHght x p y q) col elem


rbSearch : Ord elem => elem -> RBTree h col elem -> Bool
rbSearch x Empty = False
rbSearch x (Node left val _ _ right) = case compare x val of
                                      LT => rbSearch x left
                                      EQ => True
                                      GT => rbSearch x right

makeBlack : RBTree h _ elem -> RBTree h Black elem
makeBlack (Node left val _ ht right) = Node left val Black ht right
