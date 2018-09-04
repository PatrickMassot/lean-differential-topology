import analysis.topology.topological_space

import pequiv

structure phomeo α β [topological_space α] [topological_space β] extends pequiv α β :=
(to_cont : ∀ V : set β, is_open V → is_open (to_fun ⁻¹' (V ∩ range) ∩ domain))
(inv_cont : ∀ U : set α, is_open U → is_open (inv_fun ⁻¹' (U ∩ domain) ∩ range))

namespace phomeo
variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]


instance : has_coe (phomeo α β) (pequiv α β) := ⟨λ f, f.to_pequiv⟩

def symm (f : phomeo α  β) : phomeo β α :=
⟨f.to_pequiv.symm, f.inv_cont, f.to_cont⟩

lemma is_open_map {f : phomeo α β} {U : set α} (H : is_open U) : is_open (f '' (U ∩ f.domain)) :=
begin
  change is_open ((f.to_pequiv) '' (U ∩ (f.to_pequiv).domain)),
  rw pequiv.image_eq_preimage,  
  exact f.inv_cont U H
end
end phomeo
