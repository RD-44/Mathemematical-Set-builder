module Coursework where

{-
  Your task is to design a datatype that represents the mathematical concept of a (finite) set of elements (of the same type).
  We have provided you with an interface (do not change this!) but you will need to design the datatype and also 
  support the required functions over sets.
  Any functions you write should maintain the following invariant: no duplication of set elements.

  There are lots of different ways to implement a set. The easiest is to use a list
  (as in the example below). Alternatively, one could use an algebraic data type, or 
  wrap a binary search tree.
  Extra marks will be awarded for efficient implementations if appropriate.

  You are NOT allowed to import anything from the standard library or other libraries.
  Your edit of this file should be completely self-contained.

  DO NOT change the type signatures of the functions below: if you do,
  we will not be able to test them and you will get 0% for that part. While sets are unordered collections,
  we have included the Ord constraint on most signatures: this is to make testing easier.

  You may write as many auxiliary functions as you need. Please include everything in this file.
-}

{-
   PART 1.
   You need to define a Set datatype. Below is an example which uses lists internally.
   It is here as a guide, but also to stop ghci complaining when you load the file.
   Free free to change it.
-}

{-Binary tree implementation of set.
Note that Show is not derived as I defined
it later-}
data Set a = Empty | Node (Set a) a (Set a) 

{-
   PART 2.
   If you do nothing else, at least get the following two functions working. They
   are required for testing purposes.
-}

{- toList {2,1,4,3} => [1,2,3,4]
Uses setfoldr with cons to keep appending values from the
tree to accumulator which is initially an empty list-}
toList :: Set a -> [a] 
toList set = setfoldr (:) set [] 

{- fromList [2,1,1,4,5] => {2,1,4,5} 
Uses foldr to insert each element of the list 
into the empty set which builds up the tree-}
fromList :: (Ord a) => [a] -> Set a 
fromList = foldr insert Empty 

{-
   PART 3.
   Your Set should contain the following functions.
   DO NOT CHANGE THE TYPE SIGNATURES.
-}

{- Test if two sets have the same elements 
by comparing sets in list form -}
instance (Ord a) => Eq (Set a) where
  s1 == s2 = toList s1 == toList s2 

{- My own function for Show which displays a set in the
standard mathematical notation (e.g - {1, 2, 3}). 
setfoldr is used to iterate through the set and add its elements to a string. -}
instance (Show a) => Show (Set a) where
  show set = '{' : (init' (setfoldr (\x y -> (show x) ++ "," ++ y) set "") ++ "}")
            where init' :: String -> String
                  init' [] = [] --To handle the case where we display an empty set
                  init' xs = init xs

{-Allows for sets to be compared lexographically like lists. -}
instance (Ord a) => Ord (Set a) where
   seta > setb = (toList seta) > (toList setb)
   seta <= setb = (toList seta) <= (toList setb)

-- the empty set
empty :: Set a
empty = Empty

-- Set with one element
singleton :: a -> Set a
singleton x = Node empty x empty 

{- insert an element of type a into a Set
Ensures order of the tree is respected when inserting.
To prevent duplicates, the tree is simply 
returned as it is, if the same element already exists in the tree.-}
insert :: (Ord a) => a -> Set a -> Set a
insert x Empty = singleton x
insert x (Node left val right)
   | x < val = Node (insert x left) val right
   | x > val = Node left val (insert x right)
   | otherwise = Node left val right 

{- joins two Sets together using setfoldr to 
recursively insert each element of set1 into set2 
to create a new tree for the union-}
union :: (Ord a) => Set a -> Set a -> Set a
union = setfoldr insert 

{- return the common elements between two Sets
Uses setfoldr to recursively build up a tree 
from the empty set with elements from set1 that are in set2.-}
intersection :: (Ord a) => Set a -> Set a -> Set a
intersection set1 set2 = setfoldr (\x y -> if member x set2 then insert x y else y) set1 empty 

{- difference gives all the elements in Set A *not* in Set B,
Exactly like intersection but checks if each element in set1 
is NOT in set2 before inserting it.-}
difference :: (Ord a) => Set a -> Set a -> Set a
difference set1 set2 = setfoldr (\x y -> if not(member x set2) then insert x y else y) set1 empty 

{- Checks if element is in set, using setfoldr to compare 
each element of the tree with x, and using the 'or' so that 
as long as one comparison is true then True is returned. -}
member :: (Ord a) => a -> Set a -> Bool
member x set = setfoldr (\y z -> (y == x) || z) set False 

{-Gives number of elements in the Set Using setfoldr 
with the function that increments the accumulator which 
starts on zero, allowing it to recursively count up the tree.-}
cardinality :: Set a -> Int
cardinality set = setfoldr (\_ y -> 1+y) set 0 

{- Uses setfoldr to repeately insert the function evaluated at an 
element in the set into the empty set, to build up the required set.-}
setmap :: (Ord b) => (a -> b) -> Set a -> Set b
setmap f set = setfoldr (insert . f) set empty 

{-Setfoldr defined for a tree. Works by folding the right subtree
and inputting this results with the root value into the function.
Then this is made into the accumulator when setfoldr is called on the left
subtree-}
setfoldr :: (a -> b -> b) -> Set a -> b -> b
setfoldr _ Empty acc = acc
setfoldr f (Node left val right) acc = setfoldr f left (f val (setfoldr f right acc)) 

{- Checks for subset using difference:
A / B = {} if and only if A is a subset of B-}
subset :: (Ord a) => Set a -> Set a -> Bool 
subset set1 set2 = difference set1 set2 == empty 

{- powerset of a set. Uses setfoldr to first insert the last element of the given set as a 
singleton to the empty set then the second element is taken and is inserted 
as a singleton into the union of the accumulator and the set made from the 
second last element being inserted into each of the sets within the accumulator
this repeats on the third last element, etc until the first element is reached,
and the powerset is formed.-}
powerSet :: Set a -> Set (Set a)
powerSet set = insert1 empty (setfoldr append set empty)
               where append :: a -> Set (Set a) -> Set (Set a)
                     append x acc = insert1 (singleton x) (union1 (setmap1 (insert1 x) acc) acc)
                                 --Modifications of union and map to work without ord
                                 where union1 :: Set a -> Set a -> Set a
                                       union1 = setfoldr insert1
                                       setmap1 :: (a -> b) -> Set a -> Set b
                                       setmap1 f setx = setfoldr (insert1 . f) setx empty 

{- This modifies insert to work without ord only inserts
to the left of the tree as it cannot make comparisons.
A precondition is that the elements added must not already
be in the set and must be added in sorted order.
This is needed for powerSet and cartesian-}
insert1 :: a -> Set a -> Set a
insert1 x Empty = Node empty x empty
insert1 x (Node left val right) = Node (insert1 x left) val right

{- cartesian product of two sets, using list comprehension
to make a list of all the possble pairs of elements from the sets
and then converts this list into a set -}
cartesian :: Set a -> Set b -> Set (a,b)
cartesian set1 set2 = foldr insert1 empty [(x,y) | x <- (toList set1), y <- (toList set2)]  

{- partition the set into two sets, with
all elements that satisfy the predicate on the left,
and the rest on the right. Uses setfoldr and insert1 to 
filter out elements for each set in the tuple. -}
partition :: (a -> Bool) -> Set a -> (Set a, Set a)
partition cond set = (setfoldr (\x y -> if cond x then insert1 x y else y) set empty, setfoldr (\x y -> if not(cond x) then insert1 x y else y) set empty)

{-
   On Marking:
   Be careful! This coursework will be marked using QuickCheck, against Haskell's own
   Data.Set implementation. Each function will be tested for multiple properties.
   Even one failing test means 0 marks for that function.

   Marks will be lost for too much similarity to the Data.Set implementation.

   Pass: creating the Set type and implementing toList and fromList is enough for a
   passing mark of 40%.
-}
