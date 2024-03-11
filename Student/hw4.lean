def isEvenLen : String → Bool := λ s => s.length % 2 == 0

def combine : String → Bool → Bool
| f, b => and (isEvenLen f) b

def foldr {α β : Type} : (α → β → β) → β → List α → β
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)


#eval foldr combine true ["hi", "fff"]


structure my_monoid (α : Type) where
(op : α → α → α)
(id : α)
(left_id : ∀(a : α), op id a = a)
(right_id : ∀(a : α), op a id = a)

def a_monoid : my_monoid Nat := my_monoid.mk Nat.add 1 sorry sorry

#check my_monoid


def nat_add_monoid' : monoid' Nat :=
  ( Nat.add,
  0,
  λ a => by simp [Nat.mul],
  λ a => by simp,
  Nat.mul_assoc)

  #check (@Option)

  def pred : Nat → Option Nat
  | Nat.zero => Option.none
  | (Nat.succ n') => n'

  def option_map {α β : Type} : (α → β) → Option α → Option β
  | _, Option.none => Option.none
  | f, (Option.some a) => some (f a)


  inductive Tree (α : Type) : Type
  | empty
  | node : α → Tree α → Tree α → Tree α
  -- or
  -- | node (a : α) (l r : Tree α) : Tree α


  def tree_map {α β : Type} : (α → β) → Tree α → Tree β
  | _, Tree.empty => Tree.empty
  | f, (Tree.node a l r) => Tree.node (f a) (tree_map f l) (tree_map f r)

#reduce tree_map Nat.succ Tree.empty

def a_tree :=
  Tree.node
  1
  (Tree.node
  2
  Tree.empty
  Tree.empty)
  (Tree.node
  3
  Tree.empty
  Tree.empty)

#reduce tree_map Nat.succ a_tree

  -- List is a Type → Type function like List α takes in a Type (α) and returns a Type


structure functor {α β : Type} (c : Type → Type) (f : α → β) : Type where
map (f : α → β) (ic : c α) : c β

def option_functor {α β : Type} : functor Option Nat.succ := functor.mk option_map


def convert {α β : Type} (c : Type → Type) (m : @functor α β c): (f : α → β) → c α → c β
| f, c => m.map f c

inductive box (α : Type)
| contents (a : α)
