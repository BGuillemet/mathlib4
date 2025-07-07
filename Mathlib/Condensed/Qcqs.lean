/-
Copyright (c) 2025 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet
-/
import Mathlib.CategoryTheory.Closed.Types
import Mathlib.CategoryTheory.Sites.Qcqs
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.Condensed.Functors
import Mathlib.Condensed.Limits

/-!
# Quasicompact and quasiseparated condensed sets

We give properties of quasicompact, quasiseparated and qcqs condensed sets.
-/

universe u v w

open CategoryTheory Limits

namespace Condensed

attribute [local instance] Types.instConcreteCategory

variable (X : CondensedSet.{u})

noncomputable def test (j : (sectionOver X.val)ᵒᵖ) :
    (((overYoneda' X.val) ⋙ presheafToSheaf (coherentTopology CompHaus) (Type (u+1))).obj j)
    ≅ (compHausToCondensed.obj j.unop.fst.unop) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (isoSheafify _ ((isSheaf_iff_isSheaf_of_type _ _).2 (Presieve.isSheaf_comp_uliftFunctor _
    (coherentTopology.isSheaf_yoneda_obj j.unop.fst.unop)))).symm

noncomputable def sheafToPresheafCompEvaluationObjIso {n : ℕ}
    (S : (Discrete (Fin n))ᵒᵖ ⥤ CompHausᵒᵖ) (X : CondensedSet.{u}) :
    (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1))
    ⋙ (evaluation CompHausᵒᵖ (Type (u + 1))).obj (limit S)).obj X
    ≅ (limit (S ⋙ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _))).obj X :=
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite (Fin n)).symm X.val
  ((preservesLimitIso X.val S).trans (Iso.refl _)).trans (limitObjIsoLimitCompEvaluation
    (S ⋙ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)) X).symm

noncomputable def sheafToPresheafCompEvaluationLimitIso {n : ℕ}
    (S : (Discrete (Fin n))ᵒᵖ ⥤ CompHausᵒᵖ) :
    sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1))
    ⋙ (evaluation CompHausᵒᵖ (Type (u + 1))).obj (limit S)
    ≅ limit (S ⋙ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)) := by
  refine NatIso.ofComponents (sheafToPresheafCompEvaluationObjIso S) (fun {X Y} f => ?_)
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite (Fin n)).symm X.val
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite (Fin n)).symm Y.val
  ext x
  set F := S ⋙ evaluation CompHausᵒᵖ (Type (u + 1)) ⋙ (whiskeringLeft _ _ (Type (u + 1))).obj
    (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1)))
  show _ = ((limitObjIsoLimitCompEvaluation _ _).inv ≫ (limit F).map _) _
  rw [limitObjIsoLimitCompEvaluation_inv_limit_map F f]
  refine congrArg _ (Types.limit_ext _ _ _ (fun j => ?_))
  show ((preservesLimitIso Y.val S).hom ≫ (limit.π (S ⋙ Y.val) j)) _
    = (limMap (whiskerLeft F ((evaluation _ _).map f)) ≫ limit.π (F ⋙ (evaluation _ _).obj Y) j) _
  rw [limMap_π, preservesLimitIso_hom_π]
  show (f.val.app (limit S) ≫ Y.val.map (limit.π S j)) _ = _
  rw [← f.val.naturality (limit.π S j)]
  show _ = (F.obj j).map f (((preservesLimitIso X.val S).hom ≫ limit.π (S ⋙ X.val) j) x)
  rw [preservesLimitIso_hom_π]
  rfl

noncomputable def limCompEvaluationCompWhiskeringLeftSheafToPresheafIso (n : ℕ) :
    (lim (J := (Discrete (Fin n))ᵒᵖ) (C := CompHaus.{u}ᵒᵖ))
    ⋙ evaluation CompHaus.{u}ᵒᵖ (Type (u + 1))
    ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf (coherentTopology CompHaus) _)
    ≅ (whiskeringRight _ _ _).obj
    (evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)) ⋙ lim := by
  refine NatIso.ofComponents sheafToPresheafCompEvaluationLimitIso (fun {S T} f => ?_)
  ext X x
  set F := S ⋙ evaluation CompHausᵒᵖ (Type (u + 1)) ⋙ (whiskeringLeft _ _ (Type (u + 1))).obj
    (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1)))
  set G := T ⋙ evaluation CompHausᵒᵖ (Type (u + 1)) ⋙ (whiskeringLeft _ _ (Type (u + 1))).obj
    (sheafToPresheaf (coherentTopology CompHaus) (Type (u + 1)))
  have := preservesLimitsOfShape_of_equiv (Discrete.opposite (Fin n)).symm X.val
  show (limitObjIsoLimitCompEvaluation G X).inv
    ((preservesLimitIso X.val T).hom (X.val.map (limMap f) x)) =
    ((preservesLimitIso X.val S).hom ≫ (limitObjIsoLimitCompEvaluation F X).inv ≫
    (limMap (whiskerRight f (_ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)))).app X
    ≫ (𝟙 _)) x
  rw [← (limitObjIsoLimitCompEvaluation G X).hom_inv_id]
  refine congrArg _ (Types.limit_ext _ _ _ (fun j => ?_))
  show _ = ((limitObjIsoLimitCompEvaluation G X).hom ≫ limit.π (G ⋙ (evaluation _ _).obj X) j) _
  rw [limitObjIsoLimitCompEvaluation_hom_π]
  show _ = (limMap _ ≫ limit.π G j).app X _
  rw [limMap_π]
  show _ = X.val.map (f.app j) (((limitObjIsoLimitCompEvaluation F X).inv ≫ (limit.π F j).app X) _)
  rw [limitObjIsoLimitCompEvaluation_inv_π_app]
  show (X.val.map _ ≫ (preservesLimitIso X.val T).hom ≫ limit.π _ j) x =
    X.val.map (f.app j) (((preservesLimitIso X.val S).hom ≫ limit.π _ j) x)
  rw [preservesLimitIso_hom_π, preservesLimitIso_hom_π, ← X.val.map_comp]
  simp

noncomputable def limCompValNatIso {n : ℕ} (X : CondensedSet.{u}) :
    lim ⋙ X.val ≅ (whiskeringRight (Discrete (Fin n)) _ _).obj X.val ⋙ lim :=
  preservesLimitNatIso X.val

noncomputable def condensedYonedaLemma :
    compHausToCondensed.op ⋙ coyoneda
      ≅ evaluation _ _ ⋙ (whiskeringLeft _ _ _).obj (sheafToPresheaf _ _) :=
  (coherentTopology CompHaus).largeCurriedYonedaCompUliftFunctorLemma.trans
    (isoWhiskerLeft _ (isoWhiskerRight ((whiskeringRight _ _ _).mapIso uliftFunctorTrivial) _))

noncomputable def coyonedaOpCompHausToCondensedFiniteCoproductNatIso {n : ℕ}
    (S : Discrete (Fin n) ⥤ CompHaus.{u}) :
    coyoneda.obj (Opposite.op (compHausToCondensed.obj (colimit S)))
    ≅ coyoneda.obj (Opposite.op (colimit (S ⋙ compHausToCondensed))) :=
  (condensedYonedaLemma.app (Opposite.op (colimit S))).trans
    (((_ ⋙ _).mapIso (limitOpIsoOpColimit _).symm).trans
    ((sheafToPresheafCompEvaluationLimitIso S.op).trans
    (((HasLimit.isoOfNatIso (isoWhiskerLeft S.op condensedYonedaLemma.symm))).trans
    ((preservesLimitIso coyoneda (S ⋙ compHausToCondensed).op).symm.trans
    (coyoneda.mapIso (limitOpIsoOpColimit _))))))

noncomputable def coyonedaOpCompHausToCondensedFiniteCoproductNatIso' {n : ℕ}
    (S : Fin n → CompHaus.{u}) :
    coyoneda.obj (Opposite.op (compHausToCondensed.obj (∐ S)))
    ≅ coyoneda.obj (Opposite.op (∐ compHausToCondensed.obj ∘ S)) :=
  (coyonedaOpCompHausToCondensedFiniteCoproductNatIso (Discrete.functor S)).trans
    (coyoneda.mapIso (HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _).symm).op)

noncomputable def compHausToCondensedFiniteCoproductIso {n : ℕ}
    (S : Discrete (Fin n) ⥤ CompHaus.{u}) :
    compHausToCondensed.obj (colimit S) ≅ colimit (S ⋙ compHausToCondensed) :=
  (Coyoneda.fullyFaithful.preimageIso
    (coyonedaOpCompHausToCondensedFiniteCoproductNatIso S).symm).unop

noncomputable def compHausToCondensedFiniteCoproductIso' {n : ℕ} (S : Fin n → CompHaus.{u}) :
    compHausToCondensed.obj (∐ S) ≅ ∐ (compHausToCondensed.obj ∘ S) :=
  (Coyoneda.fullyFaithful.preimageIso
    (coyonedaOpCompHausToCondensedFiniteCoproductNatIso' S).symm).unop

lemma truc {n : ℕ} (S : Discrete (Fin n) ⥤ CompHaus.{u}) (j : Discrete (Fin n)) :
    compHausToCondensed.map (colimit.ι S j)
    = colimit.ι (S ⋙ compHausToCondensed) j ≫ (compHausToCondensedFiniteCoproductIso S).inv := by
  sorry

instance {n : ℕ} : PreservesColimitsOfShape (Discrete (Fin n)) compHausToCondensed where
  preservesColimit {S} := by
    refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit S) ?_
    sorry

instance : PreservesFiniteCoproducts compHausToCondensed where
  preserves := inferInstance

/- noncomputable def compHausToCondensedIsoYonedaCompUliftFunctorCompPresheafToSheaf :
    compHausToCondensed ≅ yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u + 1} ⋙ presheafToSheaf  _ _ :=
  sorry -/

theorem isQuasicompact_iff_compHaus_cover (X : CondensedSet.{u}) :
    X.Quasicompact ↔ ∃ S : CompHaus.{u}, ∃ f : compHausToCondensed.obj S ⟶ X, Epi f := by
  constructor
  · intro hX
    obtain ⟨J, hJ⟩ := hX.isQuasicompact
      (Limits.sigmaMapColim (overYoneda' X.val ⋙ presheafToSheaf _ _)
      ≫ (Sheaf.isoColimitOverYonedaCompPresheafToSheaf'.{u + 1} X).inv)
    obtain ⟨n, hn⟩ := Finite.exists_equiv_fin J
    obtain e := Classical.choice hn
    use ∐ (fun j : Fin n => (e.invFun j).val.unop.fst.unop)
    have (j : Fin n) : compHausToCondensed.obj (e.invFun j).val.unop.fst.unop
        ≅ (overYoneda' X.val ⋙ presheafToSheaf _ _).obj (e.invFun j) := by
      show compHausToCondensed.obj (e.invFun j).val.unop.fst.unop
        ≅ (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u + 1} ⋙ presheafToSheaf _ _).obj
        (e.invFun j).val.unop.fst.unop
      apply Iso.app
      exact (isoWhiskerLeft (_ ⋙ sheafCompose _ _) (sheafificationNatIso _ _)).trans
        (isoWhiskerRight
        (coherentTopology CompHaus).yonedaCompSheafComposeUliftFunctorCompSheafToPresheaf
        (presheafToSheaf _ _))
    use ((compHausToCondensedFiniteCoproductIso' _).hom
      ≫ (Sigma.mapIso this).hom
      ≫ (Sigma.whiskerEquiv (g := (overYoneda' X.val ⋙ presheafToSheaf _ _).obj ∘ Subtype.val)
      e.symm (fun _ => Iso.refl _)).hom)
      ≫ Sigma.map' Subtype.val (fun j => 𝟙 _)
      ≫ sigmaMapColim (overYoneda' X.val ⋙ presheafToSheaf _ _)
      ≫ (Sheaf.isoColimitOverYonedaCompPresheafToSheaf'.{u + 1} X).inv
    exact epi_comp' inferInstance hJ
  · intro ⟨S, f, hf⟩
    refine { isQuasicompact := fun {I G} g hg => ?_ }
    sorry
