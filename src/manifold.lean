import analysis.topology.topological_space
import analysis.real
import data.set.function
import data.equiv


open topological_space function set

universes u v w

section intersection
variables {α : Type u} (A B : set α)

/-- A ∩ B seen as a subset of A -/
def inter_left := {a : A | a.val ∈ B }

/-- A ∩ B seen as a subset of B -/
def inter_right := {b : B | b.val ∈ A }

variables {A B}
lemma mem_right_of_mem_inter_left {a : A} : a ∈ inter_left A B → a.val ∈ B := by finish

lemma mem_left_of_mem_inter_right {b : B} : b ∈ inter_right A B → b.val ∈ A := by finish
end intersection


lemma inv_mem_of_mem_image {α : Type u} {β : Type v} {f : α ≃ β} {s : set α} {b : β} (H : b ∈ f '' s) : f.inv_fun b ∈ s :=
by simpa [equiv.image_eq_preimage] using H


section atlases
variables (n : ℕ) (M : Type)

local notation `ℝ^`q := fin q → ℝ

def is_smooth {n p : ℕ} {U : set ℝ^n} {V : set ℝ^p} (op : is_open U) (f : U → V) : Prop := sorry

lemma is_smooth_comp {n p q : ℕ} {U : set ℝ^n} {V : set ℝ^p} {W : set ℝ^q} (opU : is_open U) (opV : is_open V) (f : U → V ) (g : V → W) :
  is_smooth opU f → is_smooth opV g → is_smooth opU (g ∘ f):= sorry

structure chart (n : ℕ) (X : Type) :=
(domain : set X)
(map : domain → ℝ^n)
(inj : injective map)
(open_range : is_open $ range map)

instance : has_coe_to_fun (chart n M) := ⟨_, λ φ, φ.map⟩
instance : has_mem M (chart n M) := ⟨λ x φ, x ∈ φ.domain⟩

noncomputable def transition {n p : ℕ} {X : Type} (φ : chart n X) (ψ : chart p X) : 
  φ.map '' (inter_left φ.domain ψ.domain) → (univ : set ℝ^p) :=
λ x, let rst := equiv.set.image φ (inter_left φ.domain ψ.domain) φ.inj in
    let ⟨y, p⟩ := rst.inv_fun x in ⟨ψ ⟨y, mem_right_of_mem_inter_left p⟩, by simp⟩

def is_open_intersection {n : ℕ} {X : Type} (φ ψ : chart n X) := 
is_open (φ '' (inter_left φ.domain ψ.domain))

def is_smooth_transition {n : ℕ} {X : Type} (φ ψ : chart n X) (H : is_open_intersection φ ψ) := 
is_smooth  H (transition φ ψ)

structure smooth_compatible {n : ℕ} {X : Type} (φ ψ : chart n X) : Prop := 
(open_intersection : is_open_intersection φ ψ)
(smooth_transition : is_smooth_transition φ ψ open_intersection)

class smooth_atlas :=
(charts : set (chart n M))
(covering : ∀ m : M, ∃ φ ∈ charts, m ∈ φ)
(compatibility : ∀ φ ψ ∈ charts, smooth_compatible φ ψ)

def smooth_atlas_eqv  : setoid (smooth_atlas n M) := 
⟨λ a b, ∀ (φ ∈ a.charts) (ψ ∈ b.charts), 
  (smooth_compatible φ ψ) ∧ (smooth_compatible ψ φ),
  begin
    sorry
  end⟩
end atlases

def smooth_atlas_class.to_topology {n : ℕ} {M : Type} (atlas_class : quotient $ smooth_atlas_eqv n M) : topological_space M :=
sorry

class smooth_manifold (M : Type) extends topological_space M :=
(dim : ℕ)
(atlas_class : quotient $ smooth_atlas_eqv dim M)
(is_t2 : @t2_space M (smooth_atlas_class.to_topology atlas_class))
(is_second_countable : @second_countable_topology M (smooth_atlas_class.to_topology atlas_class))
