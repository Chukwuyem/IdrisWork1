
import ChrisTreeV5

listToRBTree: Ord a => List a -> (h ** RB a Black h)
listToRBTree [] = (0 ** RBNil)
listToRBTree [s] = (1 ** BNode RBNil s RBNil)
listToRBTree (x :: xs) =
  case listToRBTree xs of
    (h ** t) =>
      case balance (insert x t) of
        (Red ** RNode l x r) => (S h ** BNode l x r)
        (Black ** t2) => (h ** t2)


  --   (h ** BNode l x r) =>
  --   (h ** RNode l x r) => S (h) ** BNode l x r
  -- fst (listToRBTree xs) ** balance (insert x (snd (listToRBTree xs)))

-- use variable to hold fst snd
-- two cases:

-- listToRBTree2: Ord a => List a -> RB a Black _
-- listToRBTree2 [] = RBNil
-- listToRBTree2 [s] = BNode RBNil s RBNil
