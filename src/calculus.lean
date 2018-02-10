import analysis.real 
import analysis.limits
import norms
import continuous_linear_maps

noncomputable theory
local attribute [instance] classical.prop_decidable

local notation f `→_{`:50 a `}`:0 b := filter.tendsto f (nhds a) (nhds b)
local notation `∥` e `∥` := norm e

section differential
variables {E : Type*} {F : Type*} {G : Type*} [normed_space ℝ E] [normed_space ℝ F] [normed_space ℝ G]

def is_differential  (f : E → F) (a : E) (L : E → F) : Prop :=
(is_bounded_linear_map L) ∧ (∃ ε : E → F, (∀ h, f (a + h) =  f a + L h + ∥h∥ • ε h) ∧  (ε →_{0} 0))

@[refl]
lemma real_refl {a:ℝ} : a ≤ a := le_refl _


open filter

lemma le_of_patrick_hyp {a b c d : ℝ} : 0 ≤ d → a ≤ b → c > 0→ a/c*d ≤ b/c*d :=
begin
intros d_nonneg a_le_b c_pos,
suffices : a/c ≤ b/c,
apply mul_le_mul_of_nonneg_right this d_nonneg,
apply div_le_of_le_mul c_pos _,
rw [←mul_div_assoc],
rw[mul_comm],
rw [mul_div_cancel],
assumption,
exact ne_of_gt c_pos,
end

@[simp]
lemma norm_norm { e : E } : ∥∥e∥∥ = ∥e∥ := 
abs_of_nonneg norm_nonneg

lemma ineq_prelim (L : E → F) (P : F → G) (ε : E → F) (η : F → G) (MP ML : ℝ) (h : E) 
(MP_pos : MP > 0)
(ineq_P : ∀ (x : F), ∥P x∥ ≤ MP * ∥x∥)
(ML_pos : ML > 0)
(ineq_L : ∀ (x : E), ∥L x∥ ≤ ML * ∥x∥)
(H : h ≠ 0) :
∥ P (ε h) + (∥L h + ∥h∥ • ε h∥ / ∥h∥) • η (L h + ∥h∥ • ε h) ∥  ≤ 
MP * ∥ε h∥ + (ML + ∥ε h∥) * ∥η (L h + ∥h∥ • ε h)∥  :=
begin
  
  have norm_h_pos : ∥h∥ > 0 := norm_pos_iff.2 H,
  have norm_h_non_zero : ∥h∥ ≠ 0 := ne_of_gt norm_h_pos,
  
  have prelim : (∥L h∥ + ∥h∥ * ∥ε h∥) / ∥h∥ * ∥η (L h + ∥h∥ • ε h)∥ ≤
          (ML * ∥h∥ + ∥h∥ * ∥ε h∥) / ∥h∥ * ∥η (L h + ∥h∥ • ε h)∥ := 
  begin
    apply le_of_patrick_hyp,
    { exact norm_nonneg },
    { specialize ineq_L h,
      apply add_le_add_right ineq_L},
    { exact norm_h_pos },
  end,
  
  have prelim2 : ∥∥L h + ∥h∥ • ε h∥ / ∥h∥∥ = ∥L h + ∥h∥ • ε h∥ / ∥h∥ := 
  begin 
    apply abs_of_nonneg,
    apply div_nonneg_of_nonneg_of_pos norm_nonneg norm_h_pos
  end,

  have prelim3 : ∥L h + ∥h∥ • ε h∥/∥h∥*∥η (L h + ∥h∥ • ε h)∥ ≤ (∥L h∥ + ∥∥h∥ • ε h∥)/∥h∥ * ∥η (L h + ∥h∥ • ε h)∥ :=
  begin
  apply le_of_patrick_hyp,
  { apply norm_nonneg },
  { apply norm_triangle },
  { apply norm_h_pos }
  end,

  exact calc 
  ∥P (ε h) + (∥L h + ∥h∥ • ε h∥ / ∥h∥) • η (L h + ∥h∥ • ε h)∥ ≤ ∥P (ε h)∥  +  ∥ (∥L h + ∥h∥ • ε h∥ / ∥h∥) • η (L h + ∥h∥ • ε h)∥ : by { simp[norm_triangle] }
  ... ≤ MP*∥ε h∥ + ∥ (∥L h + ∥h∥ • ε h∥ / ∥h∥) • η (L h + ∥h∥ • ε h)∥ : by { simp[ineq_P] }
  ... ≤ MP*∥ε h∥ + (∥L h + ∥h∥ • ε h∥ / ∥h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by { simp[norm_smul], rw[prelim2] }
  ... ≤ MP*∥ε h∥ + ((∥L h∥ + ∥ ∥h∥ • ε h∥) / ∥h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by { simp[norm_triangle], exact prelim3 }
  ... ≤ MP*∥ε h∥ + ((∥L h∥ +  ∥h∥ *∥ε h∥) / ∥h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by { simp[norm_smul (∥h∥) (ε h)]}
  ... ≤ MP*∥ε h∥ + ((ML*∥h∥ +  ∥h∥ *∥ε h∥) / ∥h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by {simp[prelim] }
  ... ≤ MP*∥ε h∥ + (ML +  ∥ε h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by { rw add_div, simp[norm_h_pos, div_self], apply mul_le_mul_of_nonneg_right _ norm_nonneg, rw[mul_div_cancel _ norm_h_non_zero], rw[mul_comm], rw[mul_div_cancel _ norm_h_non_zero] }
end


theorem chain_rule (f : E → F) (g : F → G) (a : E) (L : E → F) (P : F → G)
(D : is_differential f a L) (D' : is_differential g (f a) P) : is_differential (g ∘ f) a (P ∘ L) :=
begin
rcases D with ⟨cont_lin_L, ε, TEf, lim_ε⟩,
rcases D' with ⟨cont_lin_P, η, TEg, lim_η⟩,
unfold is_differential,
have cont_linPL := comp_continuous_linear_map L P cont_lin_L cont_lin_P,
split,
{ exact cont_linPL },
let δ := λ h, if (h = 0) then 0 else  P (ε h) + (∥ L h + ∥h∥•ε h ∥/∥h∥)• η (L h + ∥h∥•ε h),

{existsi δ,
{ split; rcases cont_lin_P with ⟨lin_P , MP, MP_pos, ineq_P⟩; rcases cont_lin_L with ⟨lin_L , ML, ML_pos, ineq_L⟩,
  { intro h,
    by_cases H : h = 0,
    { -- h = 0 case
      simp [H, cont_linPL.1.zero] },
    { -- h ≠ 0 case
      have fact1 := calc 
      (g ∘ f) (a + h) = g (f (a + h)): by refl
      ... = g (f a + L h + ∥h∥ • ε h)  : by rw TEf
      ... = g (f a + (L h + ∥h∥ • ε h)) : by {simp, }
      ... = g (f a) + P (L h + ∥h∥ • ε h) + ∥ L h + ∥h∥ • ε h∥ • η (L h + ∥h∥ • ε h) : by rw TEg
      ... = g (f a) + P (L h) + ∥h∥ • P (ε h) + ∥ L h + ∥h∥ • ε h∥ • η (L h + ∥h∥ • ε h) : by { simp[lin_P.add, lin_P.smul] },
      
      simp[δ, H, fact1], 
      -- now we only need computing and h ≠ 0
      clear fact1 lin_L ineq_L ML_pos ML lin_P ineq_P MP_pos MP cont_linPL δ TEf TEg f g lim_ε lim_η a,
      
      rw[smul_add, smul_smul],
      congr_n 1,
      apply (congr_arg (λ x, x • η (L h + ∥h∥ • ε h))),
            
      rw [←mul_div_assoc, mul_comm, mul_div_cancel],
      
      exact mt norm_zero_iff_zero.1 H },
  }, 
  { -- prove δ →_0 0
    apply tendsto_iff_norm_tendsto_zero.2,
    
    have bound_δ : ∀ h :E, ∥ δ h ∥ ≤ MP*∥ε h∥ + ( ML + ∥ε h ∥)*∥ η (L h + ∥h∥•ε h)∥,
    { intro h,
      by_cases H : h = 0,
       { -- h = 0 case
       simp [H, δ],
       simp,
       
       have h1 : 0 ≤ MP * ∥ε 0∥ := mul_nonneg (le_of_lt MP_pos) norm_nonneg,
       have h2 : 0 ≤ ML + ∥ε 0∥ := add_nonneg' (le_of_lt ML_pos) norm_nonneg,
       have h3 : 0 ≤ (ML + ∥ε 0∥) * ∥η (L 0)∥ := mul_nonneg h2 norm_nonneg,
             
       exact add_nonneg' h1 h3 },
      { -- h ≠ 0 case
        simp [δ],
        simp [H],

        apply ineq_prelim,
        repeat {assumption} },
    }, -- end of bound_δ proof
    
     
    have norm_δ_nonneg : ∀ (t : E), (0:ℝ) ≤ (λ (h : E), ∥δ h∥) t :=
    assume t, norm_nonneg,
    simp,
    apply squeeze_zero (λ h, ∥ δ h∥) (λ h, MP*∥ε h∥ + ( ML + ∥ε h ∥)*∥ η (L h + ∥h∥•ε h)∥) 0 norm_δ_nonneg bound_δ,
    clear norm_δ_nonneg bound_δ, 

    have limML : ((λ (x: E), ML) →_{0} ML) := tendsto_const_nhds,
      
    have lim_normE:= @lim_norm_zero E _,
    have lim_ML_norm := tendsto_mul limML lim_normE,
    simp at lim_ML_norm,

    have lim1 : ((λ (h: E),  L h + ∥h∥ • ε h) →_{(0:E)} 0),
    { 
      have := squeeze_zero (λ (x : E), ∥L x∥) (λ (x : E), ML*∥x∥) 0,
      simp[norm_nonneg, ineq_L] at this, clear ineq_L,
      
      simp[lim_ML_norm] at this,
      rename this lim_norm_L,
      have lim_L := (@tendsto_iff_norm_tendsto_zero _ _ _ _ L 0 0).2,
      simp at lim_L,
      specialize lim_L lim_norm_L,
      
      simpa using tendsto_add lim_L (tendsto_smul lim_normE lim_ε) },
      
    
    have lim2 := tendsto.comp lim1 lim_η, clear lim1,

    have norm_reformulation := (@tendsto_iff_norm_tendsto_zero _ _ _ _ (λ (h: E),  η (L h + ∥h∥ • ε h)) 0 0 ).1,
    simp at norm_reformulation,
    
    have lim3 : ((λ (h: E),  ∥ η (L h + ∥h∥ • ε h)∥) →_{0} (0)) :=
    norm_reformulation lim2, clear norm_reformulation, clear lim2,
    
    have lim_norm_ε : (λ (e : E), ∥ε e∥)→_{0}0 := 
    by simpa using (@tendsto_iff_norm_tendsto_zero _ _ _ _ ε 0 0 ).1 lim_ε,
    have lim4 : (λ (x : E),  ML + ∥ε x∥)→_{0} ML := 
    by simpa using tendsto_add limML lim_norm_ε,
    
    have lim5 : (λ (x : E), (∥ε x∥ + ML) * ∥η (L x + ∥x∥ • ε x)∥)→_{0}0 :=
    by simpa using tendsto_mul lim4 lim3,
    
    have limMP : ((λ (x: E), MP) →_{0} MP) := tendsto_const_nhds,
    
    have lim6 := tendsto_mul limMP lim_norm_ε,
    simp at lim6,

    have lim7:= tendsto_add lim6 lim5,
    simp at lim7,
    
    simp [lim7] } } }
end

end differential