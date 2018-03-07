import algebra.module

namespace tactic

open interactive interactive.types lean.parser
open has_map has_seq list nat

meta def mk_mvar_list : ℕ → tactic (list expr)
 | 0 := pure []
 | (succ n) := (::) <$> mk_mvar <*> mk_mvar_list n

/-- `lifted_instance [inst1,inst2]` constructs an instance of `my_class (Π i : I, f i)`
    where we know `Π i, my_class (f i)` and where all non-propositional fields are
    filled in by `inst1` and `inst2`
 -/
meta def lifted_instance (sources : parse pexpr_list_or_texpr) : tactic unit :=
do t ← target,
   e ← get_env,
   let struct_n := t.get_app_fn.const_name,
   fields ← (e.structure_fields struct_n : tactic (list name))
     <|> fail "target class is not a structure",
   st ← sources.mmap (λ s,
      do t ← to_expr s >>= infer_type,
         e.structure_fields t.get_app_fn.const_name),
   let st := st.join,
   axms ← mfilter (λ f : name,
                resolve_name (f.update_prefix struct_n) >>=
                  to_expr >>=
                  is_proof)
              (fields.diff st),
   vals ← mk_mvar_list axms.length,
   refine (pexpr.mk_structure_instance
     { struct := some struct_n
     , field_names := axms
     , field_values := vals.map to_pexpr
     , sources := sources }),
   set_goals vals,
   axms.mmap' (λ h,
     solve1 $
     do intros,
        funext,
        applyc $ h.update_prefix struct_n)

run_cmd add_interactive [`lifted_instance]

end tactic

-- following does not work, always need (x[i])
-- local notation x`[`:max i`]`:0 := x i
-- it would be nice to have a notation making it clear we don't think of x as a function

namespace indexed_product
universes u v
variable {I : Type u} -- The indexing type
variable {f : I → Type v}

instance has_mul [∀ i, has_mul $ f i] : has_mul (Π i : I, f i) :=
⟨λ x y, λ i, x i * y i⟩

instance semigroup [∀ i, semigroup $ f i] : semigroup (Π i : I, f i) :=
{ mul_assoc := assume a b c, by funext ; exact @semigroup.mul_assoc (f i) _ (a i) (b i) (c i),
  ..indexed_product.has_mul }

instance comm_semigroup [∀ i, comm_semigroup $ f i] : comm_semigroup (Π i : I, f i) :=
{ mul_comm := assume a b, by funext ; exact @comm_semigroup.mul_comm (f i) _ (a i) (b i),
  ..indexed_product.semigroup }

instance has_one [∀ i, has_one $ f i] : has_one (Π i : I, f i) :=
⟨λ i, 1⟩

instance has_inv [∀ i, has_inv $ f i] : has_inv (Π i : I, f i) :=
⟨λ x, λ i, (x i)⁻¹⟩

instance monoid [∀ i, monoid $ f i] : monoid (Π i : I, f i) :=
by lifted_instance [indexed_product.has_one,indexed_product.semigroup]

instance comm_monoid [∀ i, comm_monoid $ f i] : comm_monoid (Π i : I, f i) :=
by lifted_instance [indexed_product.monoid,indexed_product.comm_semigroup]

instance group [∀ i, group $ f i] : group (Π i : I, f i) :=
by lifted_instance [indexed_product.has_inv,indexed_product.monoid]

instance has_add [∀ i, has_add $ f i] : has_add (Π i : I, f i) :=
⟨λ x y, λ i, x i + y i⟩

instance add_semigroup [∀ i, add_semigroup $ f i] : add_semigroup (Π i : I, f i) :=
by lifted_instance [indexed_product.has_add]

instance has_zero [∀ i, has_zero $ f i] : has_zero (Π i : I, f i) :=
⟨λ i, 0⟩

instance has_neg [∀ i, has_neg $ f i] : has_neg (Π i : I, f i) :=
⟨λ x, λ i, -(x i)⟩

instance add_group [∀ i, add_group $ f i] : add_group (Π i : I, f i) :=
by lifted_instance [indexed_product.has_zero,indexed_product.has_neg,indexed_product.add_semigroup]

instance add_comm_group [∀ i, add_comm_group $ f i] : add_comm_group (Π i : I, f i) :=
by lifted_instance [indexed_product.add_group]

instance distrib [∀ i, distrib $ f i] : distrib (Π i : I, f i) :=
by lifted_instance [indexed_product.has_add,indexed_product.has_mul]

instance ring [∀ i, ring $ f i] : ring (Π i : I, f i) :=
by lifted_instance [indexed_product.distrib,indexed_product.monoid,indexed_product.add_comm_group]

instance comm_ring [∀ i, comm_ring $ f i] : comm_ring (Π i : I, f i) :=
by lifted_instance [indexed_product.comm_semigroup,indexed_product.ring]

instance has_scalar {α : Type*} [∀ i, has_scalar α $ f i] : has_scalar α (Π i : I, f i) :=
⟨λ s x, λ i, s • (x i)⟩

instance module {α : Type*} [ring α] [∀ i, module α $ f i] : module α (Π i : I, f i) :=
by lifted_instance [indexed_product.has_scalar]

instance vector_space (α : Type*) [field α] [∀ i, vector_space α $ f i] : vector_space α (Π i : I, f i) :=
{ ..indexed_product.module }
end indexed_product
