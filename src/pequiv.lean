import logic.function data.set.function
import tactic.interactive

import tactic.easy

meta def unfold_comp : tactic unit :=
`[repeat { rw comp_apply }]

open function set

universes u v w
variables {α : Type*} {β : Type*} {γ : Type*}

/-- `pequiv α β` is the type of functions from `α → β` which induce a 
    bijection from some `domain ⊆ α` to some `range ⊆ β`. -/
structure pequiv (α : Sort*) (β : Sort*) :=
(domain    : set α)
(range     : set β)
(to_fun    : α → β)
(inv_fun   : β → α)
(maps_to   : set.maps_to to_fun domain range)
(maps_inv  : set.maps_to inv_fun range domain)
(inv_inv   : inv_on inv_fun to_fun domain range)


namespace pequiv

instance : has_coe_to_fun (pequiv α β) :=
⟨_, to_fun⟩

lemma inv_inv' (f : pequiv α β) : inv_on f f.inv_fun f.range f.domain :=
⟨f.inv_inv.right, f.inv_inv.left⟩

def symm (f : pequiv α β) : pequiv β α :=
⟨f.range, f.domain, f.inv_fun, f.to_fun, f.maps_inv, f.maps_to, inv_inv' f⟩

local notation f`⁻¹` := f.symm

lemma inv_to {f : pequiv α β} {a : α} (H : a ∈ f.domain) : f.inv_fun (f.to_fun a) = a :=
f.inv_inv.1 _ H

lemma to_inv {f : pequiv α β} {b : β} (H : b ∈ f.range) : f.to_fun (f.inv_fun b) = b :=
f.inv_inv'.1 b H

lemma domain_to_range {f : pequiv α β} {x : α} (h : x ∈ f.domain) : f x ∈ f.range :=
f.maps_to h

def comp (g : pequiv β γ) (f : pequiv α β)  : pequiv α γ := 
begin
  refine_struct { 
      domain  := f.domain ∩ f.to_fun ⁻¹' (f.range ∩ g.domain),
      range   := g.to_fun '' (f.range ∩ g.domain),
      to_fun  := g.to_fun ∘ f.to_fun,
      inv_fun := f.inv_fun ∘ g.inv_fun, ..},
  { intros a _,
    existsi f a,
    easy },
  { rintro c ⟨b, ⟨⟨h, h'⟩, h''⟩⟩,
    rw mem_preimage_eq,
    split,
    { unfold_comp, 
      rw [←h'', inv_to],
      exact f.maps_inv h,
      assumption },
    { unfold_comp, 
      split ; { rw to_inv ; rw [←h'', inv_to];  assumption }}},
  { split,
    { rintro a ⟨a_in_f, f_a_in⟩,
      unfold_comp,
      repeat { rwa inv_to },
      easy },
    { rintro c ⟨b, ⟨⟨b_in_r_f, b_in_d_g⟩, g_b⟩⟩,
      unfold_comp,
      repeat { rwa to_inv },
      exact g_b ▸ domain_to_range b_in_d_g,
      rwa [←g_b, inv_to],
      assumption }}
end

local infix `∘` := comp

@[simp]
lemma comp_domain (g : pequiv β γ) (f : pequiv α β)  :
(g ∘ f).domain = f.domain ∩ f.to_fun ⁻¹' (f.range ∩ g.domain) := rfl

@[simp]
lemma inv_image_range_iff (f : pequiv α β)(x : α) : 
x ∈ f.inv_fun '' f.range ↔ x ∈ f.domain :=
begin
  split,
  { rintro ⟨y, ⟨y_in, inv_y⟩⟩,
    have := f.maps_inv y_in,
    rwa [mem_preimage_eq, inv_y] at this },
  { intro x_in,
    have := f.maps_to x_in,
    rw [mem_preimage_eq] at this,
    existsi f x,
    split, 
    assumption, 
    unfold_coes,
    rwa inv_to },
end

def id (a : set α) : pequiv α α := 
begin
  refine_struct 
  { domain  := a,
    range   := a,
    to_fun  := id,
    inv_fun := id,
     ..} ; try {split} ; intros x h ; simp *
end

@[simp]
lemma id_domain (a : set α) : (id a).domain = a := rfl

@[simp]
lemma id_range (a : set α) : (id a).range = a := rfl


@[extensionality]
lemma ext {f : pequiv α β} {g : pequiv α β}
(Hdom : f.domain = g.domain) (Hrg : f.range = g.range)
(Hto : f.to_fun = g.to_fun) (Hinv : f.inv_fun = g.inv_fun) : f = g :=
begin
  cases f, cases g,
  congr ; cc
end

lemma symm_symm (f : pequiv α β) : f.symm.symm = f :=
by ext ; refl

@[simp]
lemma symm_self_val {f : pequiv α β} {x : α} (h :x ∈ f.domain) : 
(f.symm ∘ f) x = x :=
begin
  change f.inv_fun (f.to_fun x) = x,
  rwa inv_to
end

@[simp]
lemma self_symm_val {f : pequiv α β} {x : β} (h :x ∈ f.range) : 
(f ∘ f.symm) x = x :=
begin
  change f.to_fun (f.inv_fun x) = x,
  rwa to_inv
end

lemma image_eq_preimage (f : pequiv α β) (U : set α) : f '' (U ∩ f.domain) = f.inv_fun ⁻¹' (U ∩ f.domain) ∩ f.range :=
begin
  ext x,
  split,
  { rintro ⟨y, y_in, f_y⟩,
    split ; rw ←f_y,
    { rw mem_preimage_eq,
      unfold_coes,
      rwa inv_to,
      easy },
    { apply domain_to_range,
      easy } },
  { rintro ⟨x_in, x_in'⟩,
    rw mem_preimage_eq at x_in,
    existsi f.inv_fun x,
    unfold_coes,
    rw to_inv,
    easy },  
end
end pequiv