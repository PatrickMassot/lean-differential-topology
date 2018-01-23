import algebra.group
import algebra.linear_algebra.prod_module
import analysis.metric_space
import analysis.topology.continuity
import data.prod
import tactic.norm_num

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

lemma norm_nonneg {g : G} : 0 ≤ ∥g∥ :=
by { rw[←norm_dist], exact dist_nonneg }

lemma norm_zero_iff_zero {g : G} : ∥g∥ = 0 ↔ g = 0 :=
by { rw[←norm_dist], exact dist_eq_zero_iff }

@[simp]
lemma zero_norm_zero : ∥(0:G)∥ = 0 :=
norm_zero_iff_zero.2 (by simp)

lemma norm_pos_iff {g : G} : ∥ g ∥  > 0 ↔ g ≠ 0 :=
begin
split ; intro h ; rw[←norm_dist] at *,
{ exact ne_of_dist_pos h },
{ exact dist_pos_of_ne h }
end

lemma norm_le_zero_iff {g : G} : ∥g∥ ≤ 0 ↔ g = 0 :=
by { rw[←norm_dist], exact dist_le_zero_iff }


@[simp]
lemma norm_neg {g : G} : ∥-g∥ = ∥g∥ :=
begin
  rw[show ∥g∥ = ∥g-0∥, by simp],
  rw[show ∥-g∥ = ∥0-g∥, by simp],
  repeat {rw[←norm_dist']},
  exact dist_comm 0 g
end

instance prod.normed_group {F : Type*} [normed_group F] : normed_group (G × F) :=
{norm := λ x, max ∥x.1∥ ∥x.2∥,
dist_eq := begin
  intros x y, 
  have h₁: ∥(x - y).fst∥ = ∥x.fst - y.fst∥, by simp,
  rw[←norm_dist'] at h₁,
  have h₂: ∥(x - y).snd∥ = ∥x.snd - y.snd∥, by simp,
  rw[←norm_dist'] at h₂,
  rw[h₁, h₂],
  refl
end,
to_metric_space := prod.metric_space_max,
to_add_comm_group := prod.add_comm_group }

lemma norm_proj1_le (x : G × H) : ∥x.1∥ ≤ ∥x∥ :=
begin  have : ∥x∥ = max  (∥x.fst∥) ( ∥x.snd∥) := rfl, rw this, simp[le_max_left], end

lemma norm_proj2_le (x : G × H) : ∥x.2∥ ≤ ∥x∥ :=
begin  have : ∥x∥ = max  (∥x.fst∥) ( ∥x.snd∥) := rfl, rw this, simp[le_max_right], end

lemma tendsto_iff_distance_tendsto_zero { X Y : Type*} [topological_space X] [metric_space Y]
{f : X → Y} {x : X} {y : Y}: (f →_{x} y) ↔ ((λ x', dist (f x') y) →_{x} 0) :=
begin
split,
{ intro lim,
  have := tendsto_dist lim tendsto_const_nhds, swap, exact y,
  finish[this] },
{ intro lim_dist,
  --unfold filter.tendsto at *,
  --rw nhds_eq_metric,
  admit }
end

lemma tendsto_iff_norm_tendsto_zero (f : G → H) (a : G) (b : H) : (f →_{a} b) ↔ ((λ e, ∥ f e - b ∥) →_{a} 0) :=
begin
simp only [norm_dist'.symm],
exact tendsto_iff_distance_tendsto_zero
end

#check filter.upwards_sets
lemma squeeze_zero {T : Type*} [topological_space T] (f g : T → ℝ) (t₀ : T) : 
(∀ t : T, 0 ≤ f t) → (∀ t : T, f t ≤ g t) → (g →_{t₀} 0) → (f →_{t₀} 0) :=
begin
  intros f_nonneg f_le_g lim_g,
  apply tendsto_orderable_unbounded _ _ _; try { apply_instance },
  existsi (1:ℝ), norm_num,
  existsi -(1:ℝ), norm_num,
  intros l u l_neg u_pos,

  let ε := min (-l) u,
  have ε_pos : 0 < ε := lt_min (neg_pos.2 l_neg) u_pos,
  have nhd_0 : { t | t < ε} ∈ (nhds (0:ℝ)).sets := gt_mem_nhds ε_pos,
  
  have H : {x | g x < ε} ∈ (nhds t₀).sets,
  { -- Here I want to use lim_g, don't know how
    have H1:= lim_g nhd_0,
    sorry },

  have H' : ∀ x : T, g x < ε → f x < ε :=
    assume x i, lt_of_le_of_lt (f_le_g x) i,
  
  -- Should now use filter.upwards_sets somehow
  -- Note that actually we can simplify the situation as follows:

  have h : {b | l < f b ∧ f b < u } = {b | f b < u}, 
  begin
    have h0 : ∀ b, ((l <f b) ∧ (f b < u)) ↔ f b < u :=
    begin
      intro b,
      split,
      { intro hf,
        cases hf with hl hu,
        exact hu },
      { intro h,
        simp[h, (lt_of_lt_of_le l_neg (f_nonneg b))] }
    end,
  simp[h0],
  end,
  rw h, clear h,
  
  sorry
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
{ continuous_add := begin 
apply continuous_iff_tendsto.2 _,
intro x,
have := (tendsto_iff_norm_tendsto_zero (λ (p : G × G), p.fst + p.snd) x (x.1 + x.2)).2,
apply this, clear this,
simp,
have ineq := λ e: G × G, calc
 ∥e.fst + (e.snd + (-x.fst + -x.snd))∥ = ∥(e.fst-x.fst) + (e.snd - x.snd)∥ : by simp
 ... ≤ ∥e.fst - x.fst∥ + ∥ e.snd - x.snd ∥  : norm_triangle (e.fst-x.fst) (e.snd - x.snd),

apply squeeze_zero _ _ x (by simp[norm_nonneg]) ineq,
have ineq1 : ∀ e : G × G, ∥ e.fst - x.fst∥ ≤ ∥e - x∥ := assume e, norm_proj1_le (e-x),
have lim1 : (λ e : G × G, ∥ e.fst - x.fst∥) →_{x} 0 := squeeze_zero _ _ x (by simp[norm_nonneg]) ineq1 _, 
clear ineq1,

have ineq2 : ∀ e : G × G, ∥ e.snd - x.snd∥ ≤ ∥e - x∥ := assume e, norm_proj2_le (e-x),
have lim2 : (λ e : G × G, ∥ e.snd - x.snd∥) →_{x} 0 := squeeze_zero _ _ x (by simp[norm_nonneg]) ineq2 _, 
clear ineq2, 

have := tendsto_add lim1 lim2,
simpa using this,

exact lim_norm x,
exact lim_norm x,
end }

end normed_group

class normed_ring (α : Type*) extends ring α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

variables {α : Type*} {β : Type*}

instance normed_ring.to_normed_group [H : normed_ring α] : normed_group α :=
{ to_uniform_space := H.to_uniform_space, ..H }

lemma norm_mul {α : Type*} [normed_ring α] (a b : α) : (∥a*b∥) ≤ (∥a∥) * (∥b∥) :=
normed_ring.norm_mul _ _


def prod.ring [ring α] [ring β] : ring (α × β) :=
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

-- a tribute to  abs_abs_sub_abs_le_abs_sub from core algebra.functions
lemma max_prod_prod_le_max_prod_max {α : Type*} [decidable_linear_ordered_comm_ring α] {a b c d  : α} 
(ha : 0 ≤ a) (hb : 0 ≤ b) (hd: 0 ≤ d) : max (a*b) (c*d) ≤ (max a c) * (max b d) :=
begin
  have hac : 0 ≤ max a c := le_trans ha (le_max_left a c),
  have A := le_max_left a c,
  have B := le_max_left b d,
  have AC := mul_le_mul A B hb hac,
  
  have C := le_max_right a c,
  have D := le_max_right b d,
  have CD := mul_le_mul C D hd hac,

  exact (max_le AC CD),
end

lemma max_le_max {α : Type*} [decidable_linear_ordered_comm_ring α] {a b c d  : α} 
(h1 : a ≤ b) (h2 : c ≤ d) : max a c ≤ max b d := 
max_le (le_trans h1 (le_max_left b d)) (le_trans h2 (le_max_right b d))

def prod.normed_ring [normed_ring α] [normed_ring β] : normed_ring (α × β) :=
{ norm_mul := assume x y, 
  calc
    ∥x * y∥ = ∥(x.1*y.1, x.2*y.2)∥ : rfl 
        ... = (max ∥x.1*y.1∥  ∥x.2*y.2∥) : rfl
        ... ≤ (max (∥x.1∥*∥y.1∥) (∥x.2∥*∥y.2∥)) : max_le_max (norm_mul (x.1) (y.1)) (norm_mul (x.2) (y.2))                                                   
        ... ≤ (max (∥x.1∥) (∥x.2∥)) * (max (∥y.1∥) (∥y.2∥)) : by { apply max_prod_prod_le_max_prod_max _ _ _; exact norm_nonneg }
        ... = (∥x∥*∥y∥) : rfl,
  dist_eq := normed_group.dist_eq,
  to_ring:=prod.ring,
  to_uniform_space := prod.normed_group.to_uniform_space,
..prod.normed_group,
}


class normed_field (α : Type*) extends discrete_field α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) = norm a * norm b)

instance normed_field.to_normed_ring [H : normed_field α] : normed_ring α :=
{ to_uniform_space := H.to_uniform_space,
  norm_mul := by finish[H.norm_mul],
 ..H }

class normed_space (α β : Type*) [normed_field α] extends vector_space α β, metric_space β :=
(norm : β → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_smul : ∀ a b, norm (a • b) = normed_field.norm a * norm b)

instance normed_space.to_normed_group [normed_field α] [H : normed_space α β] : normed_group β :=
{ to_uniform_space := H.to_uniform_space, ..H }

lemma norm_smul {α : Type*} { β : Type*} [normed_field α] [normed_space α β] (s : α) (x : β) : ∥s • x∥ = ∥s∥ * ∥x∥ :=
normed_space.norm_smul _ _

lemma max_monotone_fun {α : Type*} [decidable_linear_order α] {β : Type*} [decidable_linear_order β] 
{f : α → β} (H : monotone f) (a a' : α)  :  max (f a) (f a') =  f(max a a') :=
begin
by_cases a ≤ a',
{ have fa_le_fa' := H h,
  rw max_comm,
  rw max_eq_left fa_le_fa',
  have T :=  max_eq_left h,
  rw max_comm at T,
  rw T },
{ have h' : a' ≤ a := le_of_not_ge h,
  rw max_eq_left (H h'),
  rw  max_eq_left h' }
end

lemma monotone_mul_nonneg (a : ℝ) : 0 ≤ a → monotone (λ x, a*x) :=
assume a_non_neg b c b_le_c, mul_le_mul_of_nonneg_left b_le_c a_non_neg

lemma max_mul_nonneg (a b c : ℝ) : 0 ≤ a → max (a*b) (a*c) = a*(max b c) :=
assume a_nonneg, max_monotone_fun (monotone_mul_nonneg a a_nonneg) b c

variables {k : Type*} [normed_field k] {E : Type*} {F : Type*} [normed_space k E] [normed_space k F]

instance product_normed_space : normed_space k (E × F) := 
{ norm_smul := 
  begin 
    intros s x,
    cases x with x₁ x₂,
    exact calc 
      ∥s • (x₁, x₂)∥ = ∥ (s • x₁, s• x₂)∥ : rfl
      ... = max (∥s • x₁∥) (∥ s• x₂∥) : rfl
      ... = max (∥s∥ * ∥x₁∥) (∥s∥ * ∥x₂∥) : by simp[norm_smul s x₁, norm_smul s x₂]
      ... = ∥s∥ * max (∥x₁∥) (∥x₂∥) : by simp[max_mul_nonneg, norm_nonneg]
  end,
  -- I have no idea why the following two lines are necessary
  add_smul := by simp[add_smul],
  smul_add := by simp[smul_add],
  to_uniform_space := prod.normed_group.to_uniform_space,
  ..prod.normed_group, 
  ..prod.vector_space }