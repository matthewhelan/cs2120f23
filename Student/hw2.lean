def add : Nat → Nat → Nat
| f, Nat.zero => f
| f, (Nat.succ f') => Nat.succ (add f f')

#eval add 2 3
#eval add 22 3

def mul : Nat → Nat → Nat
| _, Nat.zero => Nat.zero
| n, (Nat.succ m') => n + mul n m'

#eval mul 3 5

def exp : Nat → Nat → Nat
| _, 0 => 1
| n, Nat.succ m => n * exp n m


#eval exp 2 3


def append {T : Type} : List T → List T → List T
| List.nil, b => b
| (List.cons h t), b => List.cons h (append t b)


#eval append [1,2] [3,4]
#eval append ["a", "b"] ["c", "d"]
