
module RBTree2

data Colour = Red | Black

data RBTree : Nat -> Type -> Type where
      Empty : Ord elem => RBTree Z elem
      Node : Ord elem => (left: RBTree p elem) -> (val: elem) -> (col: Colour) ->
                          (h: Nat) -> (right: RBTree q elem) -> RBTree h elem

{- this implementation includes the black height of the node, with empty node having black height 0 -}
rbSearch : Ord elem => elem -> RBTree h elem -> Bool
rbSearch x Empty = False
rbSearch x (Node left val _ _ right) = case compare x val of
                                      LT => rbSearch x left
                                      EQ => True
                                      GT => rbSearch x right

--because makeblack doesn't change black height of node
makeBlack : RBTree h elem -> RBTree h elem
makeBlack (Node left val _ ht right) = Node left val Black ht right

---balance left x col ht right => Node left val col ht right
balance : Ord elem => RBTree p elem -> elem -> Colour -> Nat -> RBTree q elem -> RBTree h elem
balance (Node (Node a x Red n b) y Red (S n) c) z Black (S (S n)) d = Node (Node a x Black n b) y Red (S n) (Node c z Black n d)
--balance (Node (Node a x Red n b) y Red o c) z Black p d = Node (Node a x Black n b) y Red o (Node c z Black n d)
balance (Node a x Red (S n) (Node b y Red n c)) z Black (S (S n)) d = Node (Node a x Black n b) y Red (S n) (Node c z Black n d)
balance a x Black (S (S n)) (Node (Node b y Red n c) z Red (S n) d) = Node (Node a x Black n b) y Red (S n) (Node c z Black n d)
balance a x Black (S (S n)) (Node b y Red (S n) (Node c z Red n d)) = Node (Node a x Black n b) y Red (S n) (Node c z Black n d)
balance left val col ht right = (Node left val col ht right)
