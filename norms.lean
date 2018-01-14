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

variables {G : Type*} [normed_group G]

lemma norm_dist' { g h : G} : dist g h = ∥g - h∥ :=
normed_group.dist_eq _ _

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

class normed_ring (α : Type*) extends ring α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

variables {α : Type*} {β : Type*}

instance normed_ring.to_normed_group [H : normed_ring α] : normed_group α :=
{ to_uniform_space := H.to_uniform_space, ..H }

instance prod.ring [ring α] [ring β] : ring (α × β) :=
{ left_distrib := assume x y z, calc
    x*(y+z) = (x.1, x.2) * (y.1 + z.1, y.2 + z.2) : by refl
    ... = (x.1*(y.1 + z.1), x.2*(y.2 + z.2)) : by refl
    ... = (x.1*y.1 + x.1*z.1, x.2*y.2 + x.2*z.2) : by simp[left_distrib],
  right_distrib := assume x y z, calc
    (x+y)*z = (x.1 + y.1, x.2 + y.2)*(z.1, z.2) : by refl
    ... = ((x.1 + y.1)*z.1, (x.2 + y.2)*z.2) : by refl
    ... = (x.1*z.1 + y.1*z.1, x.2*z.2 + y.2*z.2) : by simp[right_distrib],
  ..prod.monoid,
  ..prod.add_comm_group}
/-
instance prod.normed_ring [normed_ring α] [normed_ring β] : normed_ring (α × β) :=
{ norm_mul :=sorry,
to_ring:=prod.ring,
..prod.normed_group}

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