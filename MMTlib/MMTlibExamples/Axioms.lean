import MMTlib

/-!
# Axiom audit

A regression test: the main theorems depend only on Lean's standard axioms (`propext`,
`Quot.sound`, and in some cases `Classical.choice`).
In particular none of them depends on `sorryAx`. `#guard_msgs` makes `lake test` fail
if this changes.
-/

/-- info: 'MMT.Derivable.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.Derivable.trans

/-- info: 'MMT.IsMorphism.comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.IsMorphism.comp

/-- info: 'MMT.LF.weaken' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.LF.weaken

/-- info: 'MMT.LF.subst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.LF.subst

/-- info: 'MMT.LF.scoping' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.LF.scoping

/-- info: 'MMT.FMor.preserves' depends on axioms: [propext] -/
#guard_msgs in #print axioms MMT.FMor.preserves

/-- info: 'MMT.stlcToLF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.stlcToLF

/-- info: 'MMT.structMor_isMorphism' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.structMor_isMorphism

/-- info: 'MMT.flat_struct_eq_pushout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.flat_struct_eq_pushout

/-- info: 'MMT.pushout_universal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.pushout_universal

/-- info: 'MMT.IsPartialMorphism.comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.IsPartialMorphism.comp

/-- info: 'MMT.LinFunctor.mor_isMorphism' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.LinFunctor.mor_isMorphism

/-- info: 'MMT.PFData.mor_comp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.PFData.mor_comp

/-- info: 'MMT.Hom.FOMor.hom_isMorphism' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.Hom.FOMor.hom_isMorphism

/-- info: 'MMT.Hom.FOView.hom_isMorphism' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.Hom.FOView.hom_isMorphism

/-- info: 'MMT.LF.Checker.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.LF.Checker.check_sound

/-- info: 'MMT.LF.Checker.check_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.LF.Checker.check_complete

/-- info: 'MMT.solution_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.solution_transport

/-- info: 'MMT.elaborate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.elaborate_sound

/-- info: 'MMT.checkTheory_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.checkTheory_sound

/-- info: 'MMT.checkView_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.checkView_sound

/-- info: 'MMT.NDiagram.closure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.NDiagram.closure_iff

/-- info: 'MMT.Hom.predAx_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.Hom.predAx_typed

/-- info: 'MMT.Hom.FOMorP.hom_isMorphism' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.Hom.FOMorP.hom_isMorphism

/-- info: 'MMT.Hom.eqAx_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.Hom.eqAx_typed

/-- info: 'MMT.Hom.FOMorA.hom_isMorphism' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.Hom.FOMorA.hom_isMorphism


/-- info: 'MMT.LF.Red.confluent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.LF.Red.confluent

/-- info: 'MMT.LF.Conv.joinable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.LF.Conv.joinable

/-- info: 'MMT.LF.conv?_correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.LF.conv?_correct

/-- info: 'MMT.LF.Red.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.LF.Red.trans

/-- info: 'MMT.solveCheckP_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.solveCheckP_sound

/-- info: 'MMT.solveCheckD_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.solveCheckD_sound

/-- info: 'MMT.Derivable.subst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.Derivable.subst

/-- info: 'MMT.STLC.subst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms MMT.STLC.subst

/-- info: 'MMT.STLC.beta_typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.STLC.beta_typed

/-- info: 'MMT.STLC.TStep.typed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms MMT.STLC.TStep.typed
