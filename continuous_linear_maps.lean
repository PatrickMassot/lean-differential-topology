import norms

local notation f `→_{`:50 a `}`:0 b := filter.tendsto f (nhds a) (nhds b)


variables {k : Type*} [normed_field k] 
variables {E : Type*}  [normed_space k E] 
variables {F : Type*} [normed_space k F]
variables {G : Type*} [normed_space k G]

-- TODO: relate to is_continuous
include k
def is_continuous_linear_map (L : E → F) := (is_linear_map L) ∧  ∃ M, M > 0 ∧ ∀ x : E, ∥ L x ∥ ≤ M *∥ x ∥ 

lemma comp_continuous_linear_map (L : E → F) (P : F → G) : 
is_continuous_linear_map L → is_continuous_linear_map P → is_continuous_linear_map (P ∘ L) :=
begin
intros HL HP,
rcases HL with ⟨lin_L , M, Mpos, ineq_L⟩,
rcases HP with ⟨lin_P , M', M'pos, ineq_P⟩,
split,
{ exact is_linear_map.comp lin_P lin_L },
{ existsi M'*M,
  split,
  { exact mul_pos M'pos Mpos },
  { intro x,
    exact calc
      ∥P (L x)∥ ≤ M' * ∥L x∥ : ineq_P (L x)
            ... ≤  M'*M*∥x∥ : by simp[mul_assoc, mul_le_mul_of_nonneg_left (ineq_L x) (le_of_lt M'pos)] } }
end

lemma lim_zero_cont_lin_map (L : E → F) : is_continuous_linear_map L → (L →_{0} 0) :=
sorry