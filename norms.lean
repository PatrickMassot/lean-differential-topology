import analysis.real
import algebra.group
import algebra.linear_algebra.prod_module
import analysis.metric_space
import order.filter
import analysis.topology.continuity
import data.prod
import tactic.norm_num

import squeeze
import max_lemmas

noncomputable theory

local notation f `→_{`:50 a `}`:0 b := filter.tendsto f (nhds a) (nhds b)

class normed_group (α : Type*) extends add_comm_group α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))


def norm {G : Type*} [normed_group G] : G → ℝ := normed_group.norm 
notation `∥` e `∥` := norm e

section normed_group
variables {G : Type*} [normed_group G] {H : Type*} [normed_group H]


lemma norm_dist' { g h : G} : dist g h = ∥g - h∥ :=
normed_group.dist_eq _ _

@[simp]
lemma norm_dist { g : G} : dist g 0 = ∥g∥ :=
by { rw[norm_dist'], simp }

lemma norm_triangle (g h : G) : ∥g + h∥ ≤ ∥g∥ + ∥h∥ :=
calc 
∥g + h∥ = ∥g - (-h)∥             : by simp
   ... = dist g (-h)            : by simp[norm_dist']
   ... ≤ dist g 0 + dist 0 (-h) : by apply dist_triangle
   ... = ∥g∥ + ∥h∥               : by simp[norm_dist']

@[simp]
lemma norm_nonneg {g : G} : 0 ≤ ∥g∥ :=
by { rw[←norm_dist], exact dist_nonneg }

lemma norm_zero_iff_zero {g : G} : ∥g∥ = 0 ↔ g = 0 :=
by { rw[←norm_dist], exact dist_eq_zero }

@[simp]
lemma zero_norm_zero : ∥(0:G)∥ = 0 :=
norm_zero_iff_zero.2 (by simp)

lemma norm_pos_iff {g : G} : ∥ g ∥  > 0 ↔ g ≠ 0 :=
begin
split ; intro h ; rw[←norm_dist] at *,
{ exact dist_pos.1 h },
{ exact dist_pos.2 h }
end

lemma norm_le_zero_iff {g : G} : ∥g∥ ≤ 0 ↔ g = 0 :=
by { rw[←norm_dist], exact dist_le_zero }


@[simp]
lemma norm_neg {g : G} : ∥-g∥ = ∥g∥ :=
begin
  rw[show ∥g∥ = ∥g-0∥, by simp],
  rw[show ∥-g∥ = ∥0-g∥, by simp],
  repeat {rw[←norm_dist']},
  exact dist_comm 0 g
end

lemma norm_triangle' (g h : G) : abs(∥g∥ - ∥h∥) ≤ ∥g - h∥ := 
begin
  have ng := calc ∥g∥ = ∥g - h + h∥ : by simp
  ... ≤ ∥g-h∥ + ∥h∥ : norm_triangle _ _,
  replace ng := sub_right_le_of_le_add ng,
  have nh := calc ∥h∥ = ∥h - g + g∥ : by simp
  ... ≤ ∥h - g∥ + ∥g∥ : norm_triangle _ _
  ... = ∥-(g - h)∥ + ∥g∥ : by simp
  ... = ∥g - h∥ + ∥g∥ : by { rw [show ∥-(g - h)∥ = ∥g-h∥, from norm_neg] },
  replace nh := sub_right_le_of_le_add nh,
  replace nh : -(∥g∥ - ∥h∥) ≤ ∥g - h∥ := by simpa using nh,
  replace nh : -∥g - h∥ ≤ ∥g∥ - ∥h∥ := by simpa using neg_le_neg nh,
  exact abs_le.2 ⟨nh, ng⟩
end

instance prod.normed_group {F : Type*} [normed_group F] : normed_group (G × F) :=
{ norm := λ x, max ∥x.1∥ ∥x.2∥,
  dist_eq := assume x y, by { simp, repeat {rw norm_dist'}, simp },
  ..prod.metric_space_max,
  ..prod.add_comm_group }

lemma norm_proj1_le (x : G × H) : ∥x.1∥ ≤ ∥x∥ :=
begin  have : ∥x∥ = max  (∥x.fst∥) ( ∥x.snd∥) := rfl, rw this, simp[le_max_left], end

lemma norm_proj2_le (x : G × H) : ∥x.2∥ ≤ ∥x∥ :=
begin  have : ∥x∥ = max  (∥x.fst∥) ( ∥x.snd∥) := rfl, rw this, simp[le_max_right], end

lemma tendsto_iff_distance_tendsto_zero { X Y : Type*} [metric_space X] [metric_space Y]
{f : X → Y} {x : X} {y : Y}: (f →_{x} y) ↔ ((λ x', dist (f x') y) →_{x} 0) :=
begin
split,
{ intro lim,
  have := tendsto_dist lim tendsto_const_nhds, swap, exact y,
  finish[this] },
{ intro lim_dist,
  apply  tendsto_nhds_of_metric.2,
  have lim_dist' := tendsto_nhds_of_metric.1 lim_dist,
  have tauto : ∀ (x : X) (y : Y), dist (dist (f x) y) 0 = dist (f x) y, 
    assume x y, calc dist (dist (f x) y) 0 = abs ((dist (f x) y) - 0) : rfl
    ... = abs (dist (f x) y) : by simp
    ... = dist (f x) y : abs_of_nonneg dist_nonneg,

  -- starting from here I would like to say rw[tauto] but I can't
  intros ε ε_pos,
  rcases (lim_dist' ε ε_pos) with ⟨δ, δ_pos, prop⟩,
  existsi [δ, δ_pos],
  intros x_1 dist_x_1,
  have :=  prop dist_x_1,
  rw tauto at this,
  exact this }
end

lemma tendsto_iff_norm_tendsto_zero (f : G → H) (a : G) (b : H) : (f →_{a} b) ↔ ((λ e, ∥ f e - b ∥) →_{a} 0) :=
begin
simp only [norm_dist'.symm],
exact tendsto_iff_distance_tendsto_zero
end


lemma lim_norm (x: G) : ((λ g, ∥g-x∥) : G → ℝ) →_{x} 0 :=
begin
apply (tendsto_iff_norm_tendsto_zero _ _ _).1, 
apply continuous_iff_tendsto.1,
simp[show (λ e : G , e) = id, from rfl, continuous_id]
end

lemma lim_norm_zero  : ((λ g, ∥g∥) : G → ℝ) →_{0} 0 :=
by simpa using lim_norm (0:G)


instance normed_top_monoid  : topological_add_monoid G  := 
⟨begin 
  apply continuous_iff_tendsto.2 _,
  intro x,
  have := (tendsto_iff_norm_tendsto_zero (λ (p : G × G), p.fst + p.snd) x (x.1 + x.2)).2,
  apply this, clear this,
  simp,
  have ineq := λ e: G × G, calc
  ∥e.fst + (e.snd + (-x.fst + -x.snd))∥ = ∥(e.fst-x.fst) + (e.snd - x.snd)∥ : by simp
  ... ≤ ∥e.fst - x.fst∥ + ∥ e.snd - x.snd ∥  : norm_triangle (e.fst-x.fst) (e.snd - x.snd),

  apply squeeze_zero _ _ x (by simp) ineq,
  have ineq1 : ∀ e : G × G, ∥ e.fst - x.fst∥ ≤ ∥e - x∥ := assume e, norm_proj1_le (e-x),
  have lim1 : (λ e : G × G, ∥ e.fst - x.fst∥) →_{x} 0 := squeeze_zero _ _ x (by simp) ineq1 _, 
  clear ineq1,

  have ineq2 : ∀ e : G × G, ∥ e.snd - x.snd∥ ≤ ∥e - x∥ := assume e, norm_proj2_le (e-x),
  have lim2 : (λ e : G × G, ∥ e.snd - x.snd∥) →_{x} 0 := squeeze_zero _ _ x (by simp) ineq2 _, 
  clear ineq2, 
  have := tendsto_add lim1 lim2,
  simpa using this,

  exact lim_norm x,
  exact lim_norm x,
end⟩

instance normed_top_group  : topological_add_group G  := 
{ continuous_neg := begin
  apply continuous_iff_tendsto.2,
  intro x,
  apply (tendsto_iff_norm_tendsto_zero _ _ _).2,
  simp,
  have neg := λ (e : G), calc
  ∥ x + -e∥ = ∥ -(e -x)∥ : by simp
  ... =  ∥e - x∥ : norm_neg,
  conv in _ {rw [neg]},

  have lim_negx : (λ (e : G), -x )→_{x} -x:= tendsto_const_nhds,
  have lim_e : (λ (e : G), e )→_{x} x := continuous_iff_tendsto.1 continuous_id x,
  have := tendsto_add lim_negx lim_e,
  simp at this,
  simpa using filter.tendsto.comp this lim_norm_zero
end,
..normed_top_monoid }

end normed_group

class normed_ring (α : Type*) extends ring α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

variables {α : Type*} {β : Type*}

instance normed_ring.to_normed_group [H : normed_ring α] : normed_group α := { ..H }

lemma norm_mul {α : Type*} [normed_ring α] (a b : α) : (∥a*b∥) ≤ (∥a∥) * (∥b∥) :=
normed_ring.norm_mul _ _


instance prod.ring [ring α] [ring β] : ring (α × β) :=
{ left_distrib := assume x y z, calc
    x*(y+z) = (x.1, x.2) * (y.1 + z.1, y.2 + z.2) : rfl
    ... = (x.1*(y.1 + z.1), x.2*(y.2 + z.2)) : rfl
    ... = (x.1*y.1 + x.1*z.1, x.2*y.2 + x.2*z.2) : by simp[left_distrib],
  right_distrib := assume x y z, calc
    (x+y)*z = (x.1 + y.1, x.2 + y.2)*(z.1, z.2) : rfl
    ... = ((x.1 + y.1)*z.1, (x.2 + y.2)*z.2) : rfl
    ... = (x.1*z.1 + y.1*z.1, x.2*z.2 + y.2*z.2) : by simp[right_distrib],
  ..prod.monoid,
  ..prod.add_comm_group}

instance prod.normed_ring [normed_ring α] [normed_ring β] : normed_ring (α × β) :=
{ norm_mul := assume x y, 
  calc
    ∥x * y∥ = ∥(x.1*y.1, x.2*y.2)∥ : rfl 
        ... = (max ∥x.1*y.1∥  ∥x.2*y.2∥) : rfl
        ... ≤ (max (∥x.1∥*∥y.1∥) (∥x.2∥*∥y.2∥)) : max_le_max (norm_mul (x.1) (y.1)) (norm_mul (x.2) (y.2))                                                   
        ... ≤ (max (∥x.1∥) (∥x.2∥)) * (max (∥y.1∥) (∥y.2∥)) : by { apply max_mul_le_mul_max _ _ _; simp }
        ... = (∥x∥*∥y∥) : rfl,
  ..prod.ring,
  ..prod.normed_group }


class normed_field (α : Type*) extends discrete_field α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) = norm a * norm b)

instance normed_field.to_normed_ring [H : normed_field α] : normed_ring α :=
{ norm_mul := by finish[H.norm_mul], ..H }

instance : normed_field ℝ :=
{ norm := λ x, abs x, 
  dist_eq := assume x y, rfl,
  norm_mul := abs_mul}

-- TODO Clean following proof
/- This proof comes late because it uses that ℝ is a normed group, 
   through tendsto_iff_norm_tendsto_zero.
   Maybe we should rather have a version of tendsto_iff_norm_tendsto_zero 
   in ℝ without using the norm stuff -/
lemma norm_continuous {G : Type*} [normed_group G]: continuous ((λ g, ∥g∥) : G → ℝ) := 
begin
apply continuous_iff_tendsto.2,
intro x,
have ineq := ∀ g : G, abs(∥g∥ - ∥x∥) ≤ ∥ g -x∥,
have lim := squeeze_zero (λ g, abs(∥g∥ - ∥x∥)) _ x _ _ (lim_norm x),
  swap,
  intro t,
  exact abs_nonneg _,
  swap,
  intro t, simp, exact norm_triangle' t x,
exact (tendsto_iff_norm_tendsto_zero (λ g : G, ∥g∥) _ _).2 lim
end


class normed_space (α : out_param $ Type*) (β : Type*) [out_param $ normed_field α] extends vector_space α β, metric_space β :=
(norm : β → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_smul : ∀ a b, norm (a • b) = normed_field.norm a * norm b)

instance normed_space.to_normed_group [normed_field α] [H : normed_space α β] : normed_group β :=
by refine { add := (+),
            dist_eq := normed_space.dist_eq,
            zero := 0,
            neg := λ x, -x,
            ..H, .. }; simp

lemma norm_smul {α : Type*} { β : Type*} [normed_field α] [normed_space α β] (s : α) (x : β) : ∥s • x∥ = ∥s∥ * ∥x∥ :=
normed_space.norm_smul _ _

variables {k : Type*} [normed_field k] {E : Type*} {F : Type*} [normed_space k E] [normed_space k F]

open filter

lemma tendsto_smul {f : E → k} { g : E → F} {e : E} {s : k} {b : F} :
(f →_{e} s) → (g →_{e} b) → ((λ e, (f e) • (g e)) →_{e} s • b) := 
begin
  intros limf limg,
  apply (tendsto_iff_norm_tendsto_zero _ _ _).2,
  have ineq : ∀ x : E, _ := begin 
    intro x, exact calc 
      ∥f x • g x - s • b∥ = ∥(f x • g x - s • g x) + (s • g x - s • b)∥ : by simp[add_assoc]
                      ... ≤ ∥f x • g x - s • g x∥ + ∥s • g x - s • b∥ : norm_triangle (f x • g x - s • g x) (s • g x - s • b)
                      ... ≤ ∥f x - s∥*∥g x∥ + ∥s∥*∥g x - b∥ : by { rw [←smul_sub, ←sub_smul, norm_smul, norm_smul] },
  end,
  apply squeeze_zero,
  { intro t, exact norm_nonneg },
  { exact ineq },
  { clear ineq,
    have limf': (λ (x : E), ∥f x - s∥)→_{e}0 := (tendsto_iff_norm_tendsto_zero _ _ _).1 limf,
    have limg' := tendsto.comp limg (continuous_iff_tendsto.1 norm_continuous _),
    have limg'' : (λ (x : E), ∥g x∥)→_{e} ∥b∥, simp[limg'], clear limg',
    
    have lim1  := tendsto_mul limf' limg'', simp at lim1,
    have limg3 := (tendsto_iff_norm_tendsto_zero _ _ _).1 limg,
    have lim2  := tendsto_mul tendsto_const_nhds limg3, swap, exact ∥s∥,
    simp at lim2,
    
    have :=  tendsto_add lim1 lim2, 
    rw [show (0:ℝ) + 0 = 0, from by simp] at this,
    exact this }
end


instance product_normed_space : normed_space k (E × F) := 
{ norm_smul := 
  begin 
    intros s x,
    cases x with x₁ x₂,
    exact calc 
      ∥s • (x₁, x₂)∥ = ∥ (s • x₁, s• x₂)∥ : rfl
      ... = max (∥s • x₁∥) (∥ s• x₂∥) : rfl
      ... = max (∥s∥ * ∥x₁∥) (∥s∥ * ∥x₂∥) : by simp[norm_smul s x₁, norm_smul s x₂]
      ... = ∥s∥ * max (∥x₁∥) (∥x₂∥) : by simp[max_mul_nonneg]
  end,
  
  add_smul := by simp[add_smul], 
  -- I have no idea why by simp[smul_add] is not enough for the next goal
  smul_add := assume r x y,  show (r•(x+y).fst, r•(x+y).snd)  = (r•x.fst+r•y.fst, r•x.snd+r•y.snd), 
               from by simp[smul_add],             
  ..prod.normed_group, 
  ..prod.vector_space }