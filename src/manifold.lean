import data.set.function
import analysis.normed_space
import tactic.easy

noncomputable theory
local attribute [instance] classical.prop_decidable 

open function set

def continuous_on {α : Type*} {β : Type*} [topological_space α] [topological_space β] (U : set α) (f : α → β) :=
∀ W : set β, is_open W → is_open (f ⁻¹' W ∩ U)

section smooth_maps
universes u
variables {α : Type u} {β : Type u} {γ : Type u} [normed_space ℝ α] [normed_space ℝ β] [normed_space ℝ γ]

def smooth_at : ∀ (x : α) (f : α → β), Prop := sorry

lemma smooth_at_congr {x : α} {f g : α → β} {U : set α}  (U_nhd : U ∈ (nhds x).sets) (Hcongr : ∀ x ∈ U, f x = g x) : 
  smooth_at x f ↔ smooth_at x g :=
sorry

lemma smooth_at_comp {x} {f : α → β} {g : β → γ} : 
  smooth_at x f → smooth_at (f x) g → smooth_at x (g ∘ f) := sorry

def smooth_on (U : set α) (f : α → β) : Prop := ∀ x ∈ U, smooth_at x f

lemma cont_on_of_smooth_on {U : set α} {f : α → β} : smooth_on U f → continuous_on U f :=
sorry

variables {U : set α} {V : set β}

lemma smooth_on_comp (f : α → β) (g : β → γ) :
  smooth_on U f → smooth_on V g → f '' U ⊆ V → smooth_on U (g ∘ f) := 
assume sm_f sm_g f_U_V x x_in_U, 
  smooth_at_comp (sm_f x x_in_U) (sm_g (f x) $ f_U_V $ mem_image_of_mem f x_in_U)
end smooth_maps

section charts

structure chart (X : Type) :=
(domain : set X)
(target : Type)
[normed_target : normed_space ℝ target]
(map : X → target)
(inj : inj_on map domain)
(open_range : is_open $ map '' domain)

variables {X : Type} [inhabited X]

def chart.range (φ : chart X) := φ.map '' φ.domain
def chart.inv (φ : chart X) := inv_fun_on φ.map (φ.domain)

instance : has_coe_to_fun (chart X) := ⟨_, λ φ, φ.map⟩
instance : has_mem X (chart X) := ⟨λ x φ, x ∈ φ.domain⟩

instance chart.target_is_normed (φ : chart X) : normed_space ℝ (φ.target) :=
φ.normed_target

lemma chart.injectivity (φ : chart X) : 
 ∀ (x : X), x ∈ φ.domain → ∀ (y : X), y ∈ φ.domain → φ x = φ y → x = y := 
begin
  intros,
  apply φ.inj ; assumption
end

lemma chart_inv_chart {φ : chart X} (x ∈ φ.domain) : 
  φ.inv (φ x) = x :=
begin
  change inv_fun_on (φ.map) (φ.domain) (φ.map x) = x,  
  rw inv_fun_on_eq',
  exact chart.injectivity φ,
  assumption
end

lemma chart_chart_inv {φ : chart X} {x : φ.target} : x ∈ φ.range → φ (φ.inv x) = x
| ⟨y, ⟨y_in, φ_y⟩⟩ := inv_fun_on_eq ⟨y, ⟨y_in, φ_y⟩⟩

lemma chart.mem_inter {φ ψ : chart X} {x : X} (h : x ∈ φ) (h' : x ∈ ψ) : x ∈ φ.domain ∩ ψ.domain :=
mem_inter h h'

lemma chart.image_inter {φ : chart X} (U V : set X) : φ '' (φ.domain ∩ U) ∩ φ '' (φ.domain ∩ V) = φ '' (φ.domain ∩ U ∩ V) :=
begin
  have : ∀ (x ∈ φ.domain ∩ U) (y ∈ φ.domain ∩ V), φ x = φ y → x = y, 
  { intros x x_in y y_in,
    apply φ.injectivity,
    easy },
  have : φ '' (φ.domain ∩ V) ∩ φ '' (φ.domain ∩ U) = φ '' (φ.domain ∩ V ∩ (φ.domain ∩ U))
    := image_inter_on this,
  have tauto : φ.domain ∩ V ∩ (φ.domain ∩ U) = φ.domain ∩ U ∩ V, 
    by easy,
  rwa [inter_comm, tauto] at this
end

def transition (φ ψ : chart X) : φ.target → ψ.target :=
ψ ∘ φ.inv

lemma transition_comp (φ ψ χ : chart X) (x : φ.target) : 
  x ∈ φ '' (φ.domain ∩ ψ.domain ∩ χ.domain) → transition φ χ x = ((transition ψ χ) ∘ (transition φ ψ)) x :=
begin
  intro h,
  change χ.map (φ.inv x) =
    (χ.map ((ψ.inv) (ψ (φ.inv x)))),
  rcases h with ⟨y, ⟨⟨y_in_φ, y_in_ψ⟩, y_in_χ⟩, ψ_y⟩,
  rw chart_inv_chart,
  rw [←ψ_y, chart_inv_chart] ; assumption
end

@[simp]
lemma transition_self {φ : chart X} : ∀ y ∈ φ.range, transition φ φ y = y :=
begin
  intros,
  change φ (chart.inv φ y) = y,
  simp [chart_chart_inv, *]
end

@[simp]
lemma transition_inverse {φ ψ : chart X} {y : φ.target} (H : y ∈ φ '' (φ.domain ∩ ψ.domain)) :
  transition ψ φ (transition φ ψ y) = y  :=
begin
  change ((transition ψ φ) ∘ transition φ ψ) y = y,
  rw ←transition_comp,
  { have : y ∈ φ.range := image_subset φ (inter_subset_left _ _) H,
    simp [*] },
  have : φ.domain ∩ ψ.domain ∩ φ.domain = φ.domain ∩ ψ.domain, 
    by easy,
  simp [this, H]
end

lemma image_transition_eq_preimage {φ ψ : chart X} {U : set φ.target} : 
  U ⊆ φ '' (φ.domain ∩ ψ.domain) → (transition φ ψ) '' U = (transition ψ φ) ⁻¹' U ∩ ψ ''(φ.domain ∩ ψ.domain) :=
begin
  intro sub,
  ext x,
  split,
  { intro x_in,
    rcases x_in with ⟨y, ⟨y_in_U, tr_y_x⟩⟩,
    have : transition ψ φ x = y,
    { rw ←tr_y_x,
      exact transition_inverse (sub y_in_U) },
    split,
    { rw mem_preimage_eq,
      cc },
    { existsi φ.inv y,
      split,
      { rcases sub y_in_U with ⟨a, ⟨⟨h, h'⟩, h''⟩⟩,
        rw [←h'', chart_inv_chart] ; try { split } ; assumption },
      { exact tr_y_x } } },
  { intro h,
    cases h with tr_x_in x_in_ψ_inter,
    rw inter_comm at x_in_ψ_inter,
    existsi [transition ψ φ x, tr_x_in],
    simp[transition_inverse, *] }
end

def is_open_intersection (φ ψ : chart X) := 
is_open (φ '' (φ.domain ∩ ψ.domain))

def is_smooth_transition (φ ψ : chart X) := 
smooth_on (φ '' (φ.domain ∩ ψ.domain)) (transition φ ψ)

lemma open_transition_of_compatible {φ ψ : chart X} {U : set φ.target} : 
  is_smooth_transition ψ φ → is_open U → U ⊆ φ '' (φ.domain ∩ ψ.domain) → is_open ((transition φ ψ) '' U) :=
begin
  intros sm op sub,
  rw image_transition_eq_preimage sub,
  simpa [inter_comm] using cont_on_of_smooth_on sm U op
end

structure smooth_compatible (φ ψ : chart X) : Prop := 
(open_intersection  : is_open_intersection φ ψ)
(smooth_transition  : is_smooth_transition φ ψ)
end charts

section atlases
variables (X : Type) [inhabited X]
structure smooth_atlas :=
(charts : set (chart X))
(covering : ∀ m : X, ∃ φ ∈ charts, m ∈ φ)
(compatibility : ∀ φ ψ ∈ charts, smooth_compatible φ ψ)

lemma open_triple_intersection {φ ψ χ : chart X} :
smooth_compatible φ ψ → smooth_compatible ψ φ → smooth_compatible ψ χ → is_open (φ '' (φ.domain ∩ ψ.domain ∩ χ.domain))
 :=
begin
  intros h h' h'',
  rcases h with ⟨op_φ_ψ, smooth_φ_ψ⟩,
  rcases h' with ⟨op_ψ_φ, smooth_ψ_φ⟩,
  rcases h'' with ⟨op_ψ_χ, smooth_ψ_χ⟩,
  have op := is_open_inter op_ψ_φ op_ψ_χ,
  rw chart.image_inter at op,

  have : ψ '' (ψ.domain ∩ φ.domain ∩ χ.domain) ⊆ ψ '' (ψ.domain ∩ φ.domain) :=
    image_subset ψ (inter_subset_left _ _),
  have op := open_transition_of_compatible smooth_φ_ψ op this,
  have h : transition ψ φ '' (ψ '' (ψ.domain ∩ φ.domain ∩ χ.domain)) = φ '' (ψ.domain ∩ φ.domain ∩ χ.domain),
  { rw [←image_comp, image_eq_image_of_eq_on],
    intros x x_in,
    rcases x_in with ⟨⟨x_in_ψ, x_in_φ⟩, x_in_χ⟩,
    change φ (ψ.inv (ψ x)) = φ x,
    rwa chart_inv_chart },
  have comm : ψ.domain ∩ φ.domain ∩ χ.domain = φ.domain ∩ ψ.domain ∩ χ.domain,
    by easy,
  rwa [h, comm] at op
end

lemma smooth_atlas_eqv_aux {a b c : smooth_atlas X} {φ χ : chart X}
  (φ_in_a : φ ∈ a.charts) (χ_in_c : χ ∈ c.charts)
  (h₁ : ∀ (ψ : chart X), ψ ∈ b.charts → smooth_compatible φ ψ ∧ smooth_compatible ψ φ)
  (h₂ : ∀ (ψ : chart X), ψ ∈ b.charts → smooth_compatible ψ χ ∧ smooth_compatible χ ψ)
: smooth_compatible φ χ :=
begin
  constructor,
    { apply is_open_iff_forall_mem_open.2,
      intros x x_in,
      rcases x_in with ⟨y, ⟨y_in_φ, y_in_χ⟩, φ_y⟩,
      rcases b.covering y with ⟨ψ, ψ_in_b, y_in_ψ⟩,
      have H : φ '' (φ.domain ∩ ψ.domain ∩ χ.domain) ⊆ φ '' (φ.domain ∩ χ.domain), 
      { apply image_subset,
        intros x h,
        easy },
      existsi [φ '' (φ.domain ∩ ψ.domain ∩ χ.domain), H],
      exact ⟨open_triple_intersection X (h₁ ψ ψ_in_b).1 (h₁ ψ ψ_in_b).2 (h₂ ψ ψ_in_b).1, 
             ⟨y, by { easy}⟩⟩ },
  { intros x x_in,
    rcases x_in with ⟨y, ⟨y_in_φ, y_in_χ⟩, φ_y⟩,
    rcases b.covering y with ⟨ψ, ψ_in_b, y_in_ψ⟩,
    rcases h₁ ψ ψ_in_b with ⟨⟨op_φ_ψ, smooth_φ_ψ⟩, ⟨op_ψ_φ, smooth_ψ_φ⟩⟩,
    rcases h₂ ψ ψ_in_b with ⟨⟨op_ψ_χ, smooth_ψ_χ⟩, ⟨op_χ_ψ, smooth_χ_ψ⟩⟩,
    
    have : y ∈ φ.domain ∩ ψ.domain ∩ χ.domain,
      by easy,
    let W := φ '' (φ.domain ∩ ψ.domain ∩ χ.domain),
    have x_in_W : x ∈ W := φ_y ▸ mem_image_of_mem φ this,
    have W_nhds_x : W ∈ (nhds x).sets :=
      mem_nhds_sets (open_triple_intersection X (h₁ ψ ψ_in_b).1 (h₁ ψ ψ_in_b).2 (h₂ ψ ψ_in_b).1) x_in_W,
        
    rw smooth_at_congr W_nhds_x (transition_comp φ ψ χ),
    change smooth_at x (transition ψ χ ∘ transition φ ψ),
    apply smooth_at_comp,
    { exact smooth_φ_ψ x (φ_y ▸ mem_image_of_mem φ ⟨y_in_φ, y_in_ψ⟩) },
    { apply smooth_ψ_χ,
      existsi y,
      split,
      { easy },
      { rw ←φ_y,
        change ψ y = ψ (chart.inv φ (φ y)),
        rwa chart_inv_chart } } } 
end

def smooth_atlas_eqv : setoid (smooth_atlas X) := 
⟨λ a b, ∀ (φ ∈ a.charts) (ψ ∈ b.charts), 
  (smooth_compatible φ ψ) ∧ (smooth_compatible ψ φ),
  begin
    apply mk_equivalence,
    { intros a φ φ_in_a ψ ψ_in_a,
      exact ⟨a.compatibility φ ψ φ_in_a ψ_in_a, a.compatibility ψ φ ψ_in_a φ_in_a⟩ },
    { intros a b H ψ ψ_in_b φ φ_in_a,
      finish },
    { intros a b c h₁ h₂ φ φ_in_a χ χ_in_c,
      specialize h₁ φ φ_in_a,
      replace h₂ := λ ψ ψ_in_b, h₂ ψ ψ_in_b χ χ_in_c, 
      split, 
      exact smooth_atlas_eqv_aux X φ_in_a χ_in_c h₁ h₂,
      apply smooth_atlas_eqv_aux X χ_in_c φ_in_a, 
      swap 3,
      exact b,
      all_goals { simp * {contextual := tt} } }
  end⟩

def smooth_atlas_class.to_topology (atlas_class : quotient $ smooth_atlas_eqv X) : topological_space X :=
sorry

open topological_space
class smooth_manifold :=
(dim : ℕ)
(atlas_class : quotient $ smooth_atlas_eqv X)
(is_t2 : @t2_space X (smooth_atlas_class.to_topology X atlas_class))
(is_second_countable : @second_countable_topology X (smooth_atlas_class.to_topology X atlas_class))

end atlases
