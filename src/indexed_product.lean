import algebra.module

universes u v

def list.mmap₂' {α β γ} {m : Type u → Type v} [applicative m] (f : α → β → m γ) :
list α → list β → m punit
 | [] _ := pure punit.star
 | _ [] := pure punit.star
 | (x :: xs) (y :: ys) := f x y *> list.mmap₂' xs ys

namespace tactic

open interactive interactive.types lean.parser
open has_map has_seq list nat

private meta def fill_in_inst_aux : expr → expr → tactic expr
 | e (expr.pi n bi d b) :=
   (do v ← mk_meta_var d,
       fill_in_inst_aux (e v) (b.instantiate_var v)) <|>
   match bi with
    | binder_info.inst_implicit := e <$> mk_meta_var d
    | _ := failed
   end
 | _ _ := failed

meta def fill_in_inst (e : expr) : tactic expr :=
do t ← infer_type e,
   fill_in_inst_aux e t <|> return e

meta def mk_mvar_list : ℕ → tactic (list expr)
 | 0 := pure []
 | (succ n) := (::) <$> mk_mvar <*> mk_mvar_list n

meta def oper_spec : lean.parser (name × pexpr) :=
prod.mk <$> ident <* tk ":=" <*> texpr

meta def oper_list : lean.parser (list (name × pexpr)) :=
brackets "{" "}" $ sep_by (skip_info (tk ",")) oper_spec

/-- `lifted_instance [inst1,inst2]` constructs an instance of `my_class (Π i : I, f i)`
    where we know `Π i, my_class (f i)` and where all non-propositional fields are
    filled in by `inst1` and `inst2`
 -/
meta def indexed_product_of_instance (ops_spec : parse $ oper_list <|> pure []) : tactic unit :=
do t ← target,
   e ← get_env,
   let struct_n := t.get_app_fn.const_name,
   fields ← (e.structure_fields struct_n : tactic (list name))
     <|> fail "target class is not a structure",
   let ⟨f_spec,f_val⟩ := ops_spec.unzip,
   let fields := fields.diff (ops_spec.map prod.fst),
   axms ← mfilter (λ f : name,
                resolve_name (f.update_prefix struct_n) >>=
                  to_expr >>=
                  is_proof)
              fields,
   ops ← mfilter (λ f : name,
                bnot <$> (resolve_name (f.update_prefix struct_n) >>=
                  to_expr >>=
                  is_proof))
              fields,
   cls ← mfilter (λ f : name,
                mk_const (f.update_prefix struct_n) >>=
                  infer_type >>= instantiate_mvars >>=
                  is_class)
                ops,
   ops ← mfilter (λ f : name,
                bnot <$> (mk_const (f.update_prefix struct_n) >>=
                  infer_type >>= instantiate_mvars >>=
                  is_class))
                ops,
   let op_ref := ops.map $ λ fn, fn.update_prefix ↑("has_" ++ fn.to_string),
   ops_def ← mmap (λ (cl_fn : name), do
         op ← mk_const cl_fn,
         fill_in_inst op)
     op_ref,
   insts ← mk_mvar_list cls.length,
   vals ← mk_mvar_list axms.length,
   refine (pexpr.mk_structure_instance
     { struct := some struct_n
     , field_names :=  f_spec ++ ops ++ cls ++ axms
     , field_values := f_val ++ (ops_def ++ insts ++ vals).map to_pexpr
     , sources := [] }),
   set_goals insts,
   all_goals apply_instance,
   list.mmap₂' (λ (h : name) g, do
       set_goals [g],
       intros,
       funext,
       applyc $ h.update_prefix struct_n,
       done)
     axms vals,
   return ()

run_cmd add_interactive [`indexed_product_of_instance]

end tactic

-- following does not work, always need (x[i])
-- local notation x`[`:max i`]`:0 := x i
-- it would be nice to have a notation making it clear we don't think of x as a function

namespace indexed_product
variable {I : Type u} -- The indexing type
variable {f : I → Type v}

-- needed for `distr`
instance has_mul [∀ i, has_mul $ f i] : has_mul (Π i : I, f i) :=
⟨λ x y, λ i, x i * y i⟩

instance semigroup [∀ i, semigroup $ f i] : semigroup (Π i : I, f i) :=
by indexed_product_of_instance

instance comm_semigroup [∀ i, comm_semigroup $ f i] : comm_semigroup (Π i : I, f i) :=
by indexed_product_of_instance

instance monoid [∀ i, monoid $ f i] : monoid (Π i : I, f i) :=
by indexed_product_of_instance { one := λ _, 1 }

instance comm_monoid [∀ i, comm_monoid $ f i] : comm_monoid (Π i : I, f i) :=
by indexed_product_of_instance

instance group [∀ i, group $ f i] : group (Π i : I, f i) :=
by indexed_product_of_instance { inv := λ x, λ i, (x i)⁻¹ }

-- needed for `distr`
instance has_add [∀ i, has_add $ f i] : has_add (Π i : I, f i) :=
⟨λ x y, λ i, x i + y i⟩

instance add_semigroup [∀ i, add_semigroup $ f i] : add_semigroup (Π i : I, f i) :=
by indexed_product_of_instance

instance add_group [∀ i, add_group $ f i] : add_group (Π i : I, f i) :=
by indexed_product_of_instance { zero := λ _, 0, neg := λ x, λ i, - (x i) }

instance add_comm_group [∀ i, add_comm_group $ f i] : add_comm_group (Π i : I, f i) :=
by indexed_product_of_instance

instance distrib [∀ i, distrib $ f i] : distrib (Π i : I, f i) :=
by indexed_product_of_instance

instance ring [∀ i, ring $ f i] : ring (Π i : I, f i) :=
by indexed_product_of_instance

instance comm_ring [∀ i, comm_ring $ f i] : comm_ring (Π i : I, f i) :=
by indexed_product_of_instance

instance has_scalar {α : Type*} [∀ i, has_scalar α $ f i] : has_scalar α (Π i : I, f i) :=
⟨λ s x, λ i, s • (x i)⟩

instance module {α : Type*} [ring α] [∀ i, module α $ f i] : module α (Π i : I, f i) :=
by indexed_product_of_instance { to_has_scalar := indexed_product.has_scalar }

instance vector_space (α : Type*) [field α] [∀ i, vector_space α $ f i] : vector_space α (Π i : I, f i) :=
{ ..indexed_product.module }
end indexed_product
