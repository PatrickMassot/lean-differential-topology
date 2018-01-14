import algebra.group
import algebra.linear_algebra.prod_module
import analysis.metric_space
import data.prod

noncomputable theory

class normed_group (α : Type*) extends add_comm_group α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))


def norm {G : Type*} [normed_group G] : G → ℝ := normed_group.norm 
notation `∥` e `∥` := norm e

section normed_group
variables {G : Type*} [normed_group G]


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

-- a tribute to  abs_abs_sub_abs_le_abs_sub from core algebra.functions
lemma max_prod_prod_le_max_prod_max {α : Type*} [decidable_linear_ordered_comm_ring α] {a b c d  : α} 
{ha : 0 ≤ a } {hb : 0 ≤ b} {hd: 0 ≤ d} : max (a*b) (c*d) ≤ (max a c) * (max b d) :=
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


instance prod.normed_ring [normed_ring α] [normed_ring β] : normed_ring (α × β) :=
{ norm_mul := assume x y, 
  calc
    ∥x * y∥ = ∥(x.1*y.1, x.2*y.2)∥ : rfl 
        ... = (max ∥x.1*y.1∥  ∥x.2*y.2∥) : rfl
        ... ≤ (max (∥x.1∥*∥y.1∥) (∥x.2∥*∥y.2∥)) : max_le_max (norm_mul (x.1) (y.1)) (norm_mul (x.2) (y.2))                                                   
        ... ≤ (max (∥x.1∥) (∥x.2∥)) * (max (∥y.1∥) (∥y.2∥)) : by { refine max_prod_prod_le_max_prod_max ; exact norm_nonneg }
        ... = (∥x∥*∥y∥) : rfl,
  dist_eq := normed_group.dist_eq,
  to_ring:=prod.ring,
  to_uniform_space := prod.normed_group.to_uniform_space,
..prod.normed_group,
}

/-
class normed_field (α : Type*) extends discrete_field α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) = norm a * norm b)

instance normed_field.to_normed_ring [H : normed_field α] : normed_ring α :=
{ to_uniform_space := H.to_uniform_space, ..H }

class normed_space (α β : Type*) [normed_field α] extends vector_space α β, metric_space β :=
(norm : β → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_smul : ∀ a b, norm (a • b) = normed_field.norm a * norm b)

instance normed_space.to_normed_group [normed_field α] [H : normed_space α β] : normed_group β :=
{ to_uniform_space := H.to_uniform_space, ..H }
-/
