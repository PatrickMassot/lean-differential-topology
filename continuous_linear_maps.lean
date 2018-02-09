import norms

local notation f `→_{`:50 a `}`:0 b := filter.tendsto f (nhds a) (nhds b)


variables {k : Type*} [normed_field k] 
variables {E : Type*}  [normed_space k E] 
variables {F : Type*} [normed_space k F]
variables {G : Type*} [normed_space k G]

-- TODO: relate to is_continuous
include k
def is_bounded_linear_map (L : E → F) := (is_linear_map L) ∧  ∃ M, M > 0 ∧ ∀ x : E, ∥ L x ∥ ≤ M *∥ x ∥ 

lemma comp_continuous_linear_map (L : E → F) (P : F → G) : 
is_bounded_linear_map L → is_bounded_linear_map P → is_bounded_linear_map (P ∘ L) :=
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

lemma continuous_bounded_linear_map {L : E → F} (H : is_bounded_linear_map L) : continuous L :=
begin
  rcases H with ⟨lin, M, Mpos, ineq⟩,
  apply continuous_iff_tendsto.2,
  intro x,
  apply (tendsto_iff_norm_tendsto_zero _ _ _).2,
  replace ineq := λ e, calc ∥L e - L x∥ = ∥L (e - x)∥ : by rw [←(lin.sub e x)]
  ... ≤ M*∥e-x∥ : ineq (e-x),
  have lim1 : (λ (x:E), M) →_{x} M := tendsto_const_nhds,

  have lim2 : (λ e, e-x) →_{x} 0 := 
  begin 
    have limId := continuous_iff_tendsto.1 continuous_id x,
    have limx : (λ (e : E), -x) →_{x} -x := tendsto_const_nhds,
    have := tendsto_add limId limx, 
    simp at this,
    simpa using this,
  end,
  replace lim2 := filter.tendsto.comp lim2 lim_norm_zero,
  apply squeeze_zero,
  { simp[norm_nonneg] },
  { exact ineq },
  { simpa using tendsto_mul lim1 lim2 }
end


lemma lim_zero_bounded_linear_map {L : E → F} (H : is_bounded_linear_map L) : (L →_{0} 0) :=
by simpa [H.left.zero] using continuous_iff_tendsto.1 (continuous_bounded_linear_map H) 0