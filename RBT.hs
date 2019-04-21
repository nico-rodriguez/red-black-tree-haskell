{-# LANGUAGE DataKinds #-}

{-# LANGUAGE GADTs #-}

{-# LANGUAGE KindSignatures #-}

{-# LANGUAGE StandaloneDeriving #-}

{-# LANGUAGE TypeFamilies #-}

module RBT (Tree(..), RBT(..), insert) where

data Color :: * where
  R :: Color  -- Red color
  B :: Color  -- Black color
  deriving Show

data Nat = Z | S Nat
  deriving Show

-- A Tree of Red and Black nodes of type a. The Tree type has the color of the
-- root, the black height (maximum number of black nodes from root to leaves)
-- and the type of the info inside the nodes (Int, String, etc).
data Tree :: Color -> Nat -> * -> * where
  E   :: Ord a => Tree 'B 'Z a
  TR  :: Ord a => Tree 'B n a -> a -> Tree 'B n a -> Tree 'R n a
  TB  :: Ord a => Tree c1 n a -> a -> Tree c2 n a -> Tree 'B ('S n) a

deriving instance Show a => Show (Tree c n a)

-- Example: reverse the tree
rev :: Tree c n a -> Tree c n a
rev E          = E
rev (TR l x r) = TR (rev l) x (rev r)
rev (TB l x r) = TB (rev l) x (rev r)

-- Example: find the maximum value stored in a non-empty tree.
maxB :: Tree 'B ('S n) a -> a
maxB (TB _ x E)            = x
maxB (TB _ _ l@TB{}) = maxB l
maxB (TB _ _ l@TR{}) = maxR l

maxR :: Tree 'R n a -> a
maxR (TR _ x E)       = x
maxR (TR _ _ l@TB{})  = maxB l

-- Well formed Red-Balck Tree. The root is always Balck.
-- The black height is hidden.
data RBT :: * -> * where
  Root :: Ord a => Tree 'B m a -> RBT a
deriving instance Show a => Show (RBT a)

data SingletonColor :: Color -> * where
  SR :: SingletonColor 'R
  SB :: SingletonColor 'B
deriving instance Show (SingletonColor c)

type family IncrementBlackHeight (c :: Color) (n :: Nat) :: Nat where
  IncrementBlackHeight 'R n = n
  IncrementBlackHeight 'B n = 'S n

-- Almost Red-Black Tree. Captures the black hegith but not the fact that
-- red nodes only have black children. They are needed in the insertion,
-- because the insertion process temporary breaks the RBT invariant.
-- They may break the color invariant at the root.
data AlmostTree :: Nat -> * -> * where
  AT :: Ord a => SingletonColor c -> Tree c1 n a -> a -> Tree c2 n a ->
    AlmostTree (IncrementBlackHeight c n) a
deriving instance Show a => Show (AlmostTree n a)

-- Non-empty valid tree of unkown color. They are needed in the rebalancing
-- operation. Since the rebalancing changes the color labels, the color of the
-- root is unkown.
data HiddenTree :: Nat -> * -> * where
  HR :: Ord a => Tree 'R n a       -> HiddenTree n a
  HB :: Ord a => Tree 'B ('S n) a  -> HiddenTree ('S n) a
deriving instance Show a => Show (HiddenTree n a)

-- Split balance into four cases:
-- 1- color violation is on the left child and the root is black: balanceLB.
-- 2- color violation is on the right child and the root is black: balanceRB.
-- 3- color violation is on the left child and the root is red: balanceLR.
-- 4- color violation is on the right child and the root is red: balanceRR.
balanceLB :: AlmostTree n a -> a -> Tree c n a -> HiddenTree ('S n) a
-- the two rotation cases
balanceLB (AT SR (TR l2 x2 r2) x1 r1) x r = HR $ TR (TB l2 x2 r2) x1 (TB r1 x r)
balanceLB (AT SR l1 x1 (TR l2 x2 r2)) x r = HR $ TR (TB l1 x1 l2) x2 (TB r2 x r)
--cases without color violation
balanceLB (AT SR E x1 E) x r = HB $ TB (TR E x1 E) x r
balanceLB (AT SR (TB l21 x21 r21) x1 (TB l22 x22 r22)) x r =
  HB $ TB (TR (TB l21 x21 r21) x1 (TB l22 x22 r22)) x r
balanceLB (AT SB l1 x1 r1) x r = HB $ TB (TB l1 x1 r1) x r

balanceRB :: Tree c n a -> a -> AlmostTree n a -> HiddenTree ('S n) a
-- the two rotation cases
balanceRB l x (AT SR l1 x1 (TR l2 x2 r2)) = HR $ TR (TB l x l1) x1 (TB l2 x2 r2)
balanceRB l x (AT SR (TR l2 x2 r2) x1 r1) = HR $ TR (TB l x l2) x2 (TB r2 x1 r1)
-- cases without color violation
balanceRB l x (AT SR E x1 E) = HB $ TB l x (TR E x1 E)
balanceRB l x (AT SR (TB l21 x21 r21) x1 (TB l22 x22 r22)) =
  HB $ TB l x (TR (TB l21 x21 r21) x1 (TB l22 x22 r22))
balanceRB l x (AT SB l1 x1 r1) = HB $ TB l x (TB l1 x1 r1)

balanceLR :: HiddenTree n a -> a -> Tree c n a -> AlmostTree n a
balanceLR (HR l) x r = AT SR l x r
balanceLR (HB l) x r = AT SR l x r

balanceRR :: Tree c n a -> a -> HiddenTree n a -> AlmostTree n a
balanceRR l x (HR r) = AT SR l x r
balanceRR l x (HB r) = AT SR l x r

-- Insert a node to a Red-Black Tree, received as a Tree, and return a tree
-- that is almost a Red-Black Tree.
insertAny :: Ord a => Tree c n a -> a -> AlmostTree n a
insertAny (TR l y r) x = case compare x y of  -- use Ord instance of a
  LT -> balanceLR (insertBlack l x) y r
  GT -> balanceRR l y (insertBlack r x)
  EQ -> AT SR l y r
insertAny E          x = forget $ insertBlack E x
insertAny (TB l y r) x = forget $ insertBlack (TB l y r) x

-- Insert a node in a balanced tree, receied as a Tree (root is black).
insertBlack :: Tree 'B n a -> a -> HiddenTree n a
insertBlack E           x = HR (TR E x E)
insertBlack (TB l y r)  x = case compare x y of
  LT -> balanceLB (insertAny l x) y r
  GT -> balanceRB l y (insertAny r x)
  EQ -> HB $ TB l y r

-- Forget that the root node satisfies the color invariant.
forget :: HiddenTree n a -> AlmostTree n a
forget (HR (TR l x r)) = AT SR l x r
forget (HB (TB l x r)) = AT SB l x r

-- Change the root node's color to black.
blacken :: AlmostTree n a -> RBT a
blacken (AT _ l x r) = Root $ TB l x r

-- Insertion preserves the Red-Black Tree invariant.
insert :: RBT a -> a -> RBT a
insert (Root t) x = blacken $ insertAny t x
