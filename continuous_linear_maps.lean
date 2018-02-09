import norms

noncomputable theory
local attribute [instance] classical.prop_decidable

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

-- Next lemma is stated for real normed space but it would work as soon as the base field is an extension of ℝ
lemma bounded_continuous_linear_map {E : Type*}  [normed_space ℝ E] {F : Type*}  [normed_space ℝ F] {L : E → F} 
(lin : is_linear_map L) (cont : continuous L ) : is_bounded_linear_map L :=
begin
  split,
  exact lin,

  replace cont := continuous_of_metric.1 cont 1 (by norm_num),
  swap, exact 0,
  rw[lin.zero] at cont,
  --have fact : ∃ (δ : ℝ) (δ_pos : δ > 0), (∀ (e : E), ∥e∥ ≤ δ → ∥L e∥ ≤ 1),
  rcases cont with ⟨δ, δ_pos, H⟩,
  revert H,
  repeat { conv in (_ < _ ) { rw norm_dist } },
  intro H,
  existsi (2/δ),
  split,
  exact div_pos two_pos δ_pos,
  intro x,
  by_cases h : x = 0,
  { simp [h, lin.zero] }, -- case x = 0
  { -- case x ≠ 0   
    have two_norm_x_pos : 2*∥x∥ > 0 := mul_pos two_pos (norm_pos_iff.2 h),
    let p := 2*∥x∥/δ,
    have p_pos : p > 0 := div_pos two_norm_x_pos δ_pos,
    let q := δ/(2*∥x∥),
    have q_pos : q > 0 := div_pos δ_pos two_norm_x_pos,
    have triv : p*q = (1:ℝ) := sorry,

    have norm_x : ∥x∥ ≠ 0 := mt norm_zero_iff_zero.1 h,
    
    have norm_calc := calc ∥(δ/(2*∥x∥))•x∥ = abs(δ/(2*∥x∥))*∥x∥ : by {rw norm_smul, refl}
    ... = δ/(2*∥x∥)*∥x∥ : by rw [abs_of_nonneg $ le_of_lt q_pos]
    ... = δ/2 : sorry
    ... < δ : sorry,
    
  exact calc 
  ∥L x∥ = ∥L (1•x)∥: by simp
  ... = ∥L ((p*q)•x) ∥ : by {rw [←triv] }
  ... = ∥L (p•q•x) ∥ : by rw mul_smul
  ... = ∥p•L (q•x) ∥ : by rw lin.smul
  ... = abs(p)*∥L (q•x) ∥ : by { rw norm_smul, refl}
  ... = p*∥L (q•x) ∥ : by rw [abs_of_nonneg $ le_of_lt $ p_pos]
  ... ≤ p*1 : le_of_lt $ mul_lt_mul_of_pos_left (H norm_calc) p_pos 
  ... = (2*∥x∥)/δ : by simp
  ... = (2/δ)*∥x∥ : sorry,
}
end