def isEvenLen : String → Bool := λ s => s.length % 2 == 0

def combine : String → Bool → Bool
| _, false => false
| f, true => isEvenLen f

def foldr {α β : Type} : (α → β → β) → β → List α → β
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)


#eval foldr combine true ["hi", "ffff"]
