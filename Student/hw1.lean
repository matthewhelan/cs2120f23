def square (n : Nat) : Nat := n^2
def inc (n : Nat) : Nat := Nat.succ n

def apply_4 {α : Type} : (α → α) → (α → α)
| f => f ∘ f ∘ f ∘ f

def apply_4' {α : Type} : (α → α) → (α → α)
| f => (λ a => (f ∘ f ∘ f ∘ f) a)

#reduce apply_4 inc 5


def compn {α : Type} : Nat → (α → α) → (α → α)
| Nat.zero, f => λ a => a
| (Nat.succ n'), f => λ a => f (compn n' f a)

#eval (compn 7 Nat.succ) 0
#eval (compn 5 square) 2


def compn' {α : Type} : Nat → (α → α) → (α → α)
| Nat.zero, f => λ a => a
| (Nat.succ n'), f => f ∘ compn' n' f

#eval (compn' 7 Nat.succ) 1
#eval (compn' 5 square) 2

def my_comp(α β γ : Type) : (β → γ) → (α → β) → (α → γ)
| f, g => λ a => f (g a)



#check List


def e : List Nat := List.nil
def l1 : List Nat := List.cons 1 e

def list_len {α : Type} : List α → Nat
| List.nil => 0
| (List.cons _ t) => 1 + list_len t

#eval list_len [1, 1]
#eval list_len e
