import data.set.basic


section
open tactic monad expr
/-- Recursively destructs all hypotheses that are conjunctions. From programming in Lean. -/
meta def destruct_conjunctions : tactic unit :=
repeat (do
  l ← local_context,
  first $ l.map (λ h, do
    ht ← infer_type h >>= whnf,
    match ht with
    | `(and %%a %%b) := do
      n ← get_unused_name `h none,
      mk_mapp ``and.left [none, none, some h] >>= assertv n a,
      n ← get_unused_name `h none,
      mk_mapp ``and.right [none, none, some h] >>= assertv n b,
      clear h
    | _ := failed
    end))

/-- Simplify proving intersection and conjunctions goals -/
meta def simp_inter : tactic unit :=
`[  destruct_conjunctions, 
    try { ext } ; try { split } ; try { intros }; destruct_conjunctions,
    all_goals { repeat { split } ; assumption }]
end

section examples
variables {α : Type*} (a b c : set α) (x : α)

example : a ∩ b ∩ c = c ∩ b ∩ a :=
by simp_inter


example : a ∩ b ∩ a = a ∩ b :=
by simp_inter

example : a ∩ b ∩ (a ∩ c) = a ∩ b ∩ c :=
by simp_inter

example (x ∈ a ∩ b ∩ c) : x ∈ b :=
by simp_inter

example (x ∈ a ∩ b ∩ c) : x ∈ b ∩ a :=
by simp_inter

example (h : x ∈ a) (h' : x ∈ b) (h'' : x ∈ c) : x ∈ b ∩ a :=
by simp_inter

example : x ∈ a →  x ∈ b →  x ∈ c → x ∈ b ∩ a :=
by simp_inter
end examples
