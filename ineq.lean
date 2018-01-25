import analysis.real

open tactic monad expr

meta def ineq_trans : tactic unit :=
do
  l ← local_context,
  first $ l.map (λ h, do
    try `[unfold gt],
    ht ← infer_type h,
    match ht with
    | `(%%a ≤ %%b) := do
        first $ l.map (λ h', do
          h't ← infer_type h',
          match h't with
          | `(has_le.le %%c %%d) := 
            if c = b then mk_app ``le_trans [h, h'] >>= exact else failed
          | `(%%c < %%d) := 
            if c = b then mk_app ``lt_of_le_of_lt [h, h'] >>= exact else failed 
          | _ := failed
          end)
    | `(%%a < %%b) := do
        --trace (to_string h ++ " : " ++ to_string ht),
        first $ l.map (λ h', do
          h't ← infer_type h',
          
          match h't with
          | `(%%c ≤ %%d) := do
            --trace (to_string h ++ " then " ++ to_string h' ++ " : " ++ to_string h't),  
            --trace ("Values c : " ++  to_string c ++ " b : " ++ to_string b),
            if c = b then mk_app ``lt_of_lt_of_le [h, h'] >>= exact else failed
          | `(%%c < %%d) := 
            if c = b then mk_app ``lt_trans [h, h'] >>= exact else failed 
          | _ := failed
          end)
    | _ := failed
    end)

section
variables {α : Type*} [decidable_linear_ordered_comm_group α]
variables (a b c d : α)

example (h : a ≤ b) (h2 : b ≤ d) : a ≤ d :=
by ineq_trans

example (h : a ≤ b) (h2 : b < d) : a < d :=
by ineq_trans

example (h : a < min b c) (h2 : min b c ≤ d) : a < d :=
by ineq_trans

example (h : a < b) (h2 :  b < d) : a < d :=
by ineq_trans

example (h : a < b) (h2 :  d > b) : a < d :=
sorry --by ineq_trans
end

variables (A B C D : ℝ)
example (h : A ≤ B) (h2 : B ≤ D) : A ≤ D :=
by ineq_trans

-- example which does not work in sqeeze.lean seems ok here
variables (X : Type) (x : X) (f g : X → ℝ) (ε y : ℝ)
example (sub_f_gt : -ε < f x - y) (tmp : f x - y ≤ g x - y) : -ε < g x - y :=
by ineq_trans

