import data.set.basic

meta def easy : tactic unit :=
`[all_goals { try { ext }, try { dsimp at * }, tauto }]

section examples
variables {α : Type*} (a b c : set α) (x : α)

example : a ∩ b ∩ c = c ∩ b ∩ a :=
by easy


example : a ∩ b ∩ a = a ∩ b :=
by easy

example : a ∩ b ∩ (a ∩ c) = a ∩ b ∩ c :=
by easy

example (x ∈ a ∩ b ∩ c) : x ∈ b :=
by easy

example (x ∈ a ∩ b ∩ c) : x ∈ b ∩ a :=
by easy

example (h : x ∈ a) (h' : x ∈ b) (h'' : x ∈ c) : x ∈ b ∩ a :=
by easy

example : x ∈ a →  x ∈ b →  x ∈ c → x ∈ b ∩ a :=
by easy
end examples

section tauto₀
variables p q r : Prop
variables h : p ∧ q ∨ p ∧ r
include h
example : p ∧ p :=
by easy

end tauto₀

section tauto₁
variables α : Type
variables p q r : α → Prop
variables h : (∃ x, p x ∧ q x) ∨ (∃ x, p x ∧ r x)
include h
example : ∃ x, p x :=
by easy

end tauto₁

section tauto₂
variables α : Type
variables x : α
variables p q r : α → Prop
variables h₀ : (∀ x, p x → q x → r x) ∨ r x
variables h₁ : p x
variables h₂ : q x

include h₀ h₁ h₂
example : ∃ x, r x :=
by easy

end tauto₂