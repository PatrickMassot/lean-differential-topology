import analysis.real 
import analysis.limits
import norms
import continuous_linear_maps

noncomputable theory
local attribute [instance] classical.prop_decidable

open filter is_bounded_linear_map

local notation f `→_{`:50 a `}`:0 b := filter.tendsto f (nhds a) (nhds b)
local notation `lim_{`:50 a`}`:0 f := lim (map f (nhds a))
local notation `∥` e `∥` := norm e

section differential
variables {E : Type*} {F : Type*} {G : Type*} [normed_space ℝ E] [normed_space ℝ F] [normed_space ℝ G]

def is_differential  (f : E → F) (a : E) (L : E → F) : Prop :=
(is_bounded_linear_map L) ∧ (∃ ε : E → F, (∀ h, f (a + h) =  f a + L h + ∥h∥ • ε h) ∧  (ε →_{0} 0))


lemma div_mul_le_div_mul_left {a b c d : ℝ} : 0 ≤ d → a ≤ b → c > 0 → a/c*d ≤ b/c*d :=
assume d0 ab c0, mul_le_mul_of_nonneg_right (div_le_div_of_le_of_pos ab c0) d0

@[simp]
lemma norm_norm { e : E } : ∥∥e∥∥ = ∥e∥ := 
abs_of_nonneg norm_nonneg

theorem chain_rule (f : E → F) (g : F → G) (a : E) (L : E → F) (P : F → G)
(D : is_differential f a L) (D' : is_differential g (f a) P) : is_differential (g ∘ f) a (P ∘ L) :=
begin
rcases D with ⟨cont_lin_L, ε, TEf, lim_ε⟩,
rcases D' with ⟨cont_lin_P, η, TEg, lim_η⟩,
unfold is_differential,
have cont_linPL := is_bounded_linear_map.comp cont_lin_L cont_lin_P,
split,
{ exact cont_linPL },
{ rcases cont_lin_P with ⟨lin_P , MP, MP_pos, ineq_P⟩,
  rcases cont_lin_L with ⟨lin_L , ML, ML_pos, ineq_L⟩,
  
  let δ := λ h, if (h = 0) then 0 else  P (ε h) + (∥ L h + ∥h∥•ε h ∥/∥h∥)• η (L h + ∥h∥•ε h),
  existsi δ,
  
  split, 
  { -- prove (g ∘ f) (a + h) = (g ∘ f) a + (P ∘ L) h + ∥h∥ • δ h
    intro h,
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
    simp,
    have bound_δ : ∀ h :E, ∥ δ h ∥ ≤ MP*∥ε h∥ + ( ML + ∥ε h ∥)*∥ η (L h + ∥h∥•ε h)∥,
    { intro h,
      by_cases H : h = 0,
      { -- h = 0 case
       
        simp [δ],
        simp [H],
        apply add_nonneg'; apply mul_nonneg,

        exact le_of_lt MP_pos,
        exact norm_nonneg,
        exact add_nonneg' (le_of_lt ML_pos) norm_nonneg,
        exact norm_nonneg },
      { -- h ≠ 0 case
        simp [δ],
        simp [H],

        have norm_h_pos : ∥h∥ > 0 := norm_pos_iff.2 H,
        have norm_h_non_zero : ∥h∥ ≠ 0 := ne_of_gt norm_h_pos,
        have prelim1 : ∥∥L h + ∥h∥ • ε h∥ / ∥h∥∥ = ∥L h + ∥h∥ • ε h∥ / ∥h∥ := 
          abs_of_nonneg (div_nonneg_of_nonneg_of_pos norm_nonneg norm_h_pos),
        have prelim2 : ∥L h + ∥h∥ • ε h∥/∥h∥*∥η (L h + ∥h∥ • ε h)∥ ≤ (∥L h∥ + ∥∥h∥ • ε h∥)/∥h∥ * ∥η (L h + ∥h∥ • ε h)∥ :=
          div_mul_le_div_mul_left norm_nonneg (norm_triangle _ _) norm_h_pos,
        have prelim3 : (∥L h∥ + ∥h∥ * ∥ε h∥) / ∥h∥ * ∥η (L h + ∥h∥ • ε h)∥ ≤
                (ML * ∥h∥ + ∥h∥ * ∥ε h∥) / ∥h∥ * ∥η (L h + ∥h∥ • ε h)∥ := 
          div_mul_le_div_mul_left norm_nonneg (add_le_add_right (ineq_L h) _) norm_h_pos,

        exact calc 
        ∥P (ε h) + (∥L h + ∥h∥ • ε h∥ / ∥h∥) • η (L h + ∥h∥ • ε h)∥ 
            ≤ ∥P (ε h)∥  +  ∥ (∥L h + ∥h∥ • ε h∥ / ∥h∥) • η (L h + ∥h∥ • ε h)∥ : by simp[norm_triangle] 
        ... ≤ MP*∥ε h∥ + (∥L h + ∥h∥ • ε h∥ / ∥h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by simp[norm_triangle, ineq_P, norm_smul, prelim1] 
        ... ≤ MP*∥ε h∥ + ((∥L h∥ + ∥ ∥h∥ • ε h∥) / ∥h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by simp[norm_triangle, prelim2]
        ... ≤ MP*∥ε h∥ + ((ML*∥h∥ +  ∥h∥ *∥ε h∥) / ∥h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by simp[norm_smul, prelim3]
        ... = MP*∥ε h∥ + (ML +  ∥ε h∥)*∥h∥ / ∥h∥ * ∥ η (L h + ∥h∥ • ε h)∥ : by simp[mul_comm, add_mul]
        ... = MP*∥ε h∥ + (ML +  ∥ε h∥) * ∥ η (L h + ∥h∥ • ε h)∥ : by simp[mul_div_cancel _ norm_h_non_zero] },
    }, -- end of bound_δ proof
    
    
    apply squeeze_zero, 
    exact assume t, norm_nonneg,
    exact bound_δ, 
    rw [show (0:ℝ) = 0 + 0, by simp],
    apply tendsto_add _ _,
    { apply_instance },
    { have limMP : (λ (h : E), MP) →_{0} MP := tendsto_const_nhds,
      simpa using tendsto_mul limMP (tendsto_iff_norm_tendsto_zero.1 lim_ε) },
    { rw [show (0:ℝ) = ML*0, by simp],
      apply tendsto_mul _ _,
      { apply_instance },
      { have limML : (λ (h : E), ML) →_{0} ML := tendsto_const_nhds,
        simpa using tendsto_add limML (tendsto_iff_norm_tendsto_zero.1 lim_ε) },
      { have lim1 := tendsto_add (lim_zero_bounded_linear_map ⟨lin_L , ML, ML_pos, ineq_L⟩) (tendsto_smul lim_norm_zero lim_ε),
        simp at lim1,
        have := tendsto.comp lim1 lim_η,
        exact tendsto.comp this lim_norm_zero } },
    } } 
end

end differential
