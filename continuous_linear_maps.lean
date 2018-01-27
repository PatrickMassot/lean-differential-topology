import norms

local notation f `→_{`:50 a `}`:0 b := filter.tendsto f (nhds a) (nhds b)


variables {k : Type*} [normed_field k] 
variables {E : Type*}  [normed_space k E] 
variables {F : Type*} [normed_space k F]
variables {G : Type*} [normed_space k G]

-- TODO: relate to is_continuous
def is_continuous_linear_map (L : E → F) := (is_linear_map L) ∧  ∃ M, M > 0 ∧ ∀ x : E, ∥ L x ∥ ≤ M *∥ x ∥ 

-- TODO: Clean up this proof
lemma comp_continuous_linear_map (L : E → F) (P : F → G) : 
is_continuous_linear_map L → is_continuous_linear_map P → is_continuous_linear_map (P ∘ L) :=
begin
intros HL HP,
rcases HL with ⟨lin_L , M, Mpos, ineq_L⟩,
rcases HP with ⟨lin_P , M', M'pos, ineq_P⟩,
split,
{ exact is_linear_map.comp lin_P lin_L },
{ existsi M*M',
  split,
  { exact mul_pos Mpos M'pos },
  { unfold function.comp,
    intro x,
    specialize ineq_P (L x),
    specialize ineq_L x,
    have fact : M'*∥L x∥ ≤ M * M' * ∥x∥ := -- prepare for PAIN
      begin 
      have ineq := mul_le_mul_of_nonneg_left ineq_L (le_of_lt M'pos),
      rw mul_comm, 
      rw mul_comm at ineq, 
      rw ←mul_assoc at ineq,
      rw mul_comm M,  
      exact ineq
      end ,
    exact le_trans ineq_P fact }
   }
end

lemma lim_zero_cont_lin_map (L : E → F) : is_continuous_linear_map L → (L →_{0} 0) :=
sorry