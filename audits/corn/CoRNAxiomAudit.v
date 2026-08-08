Require Import CoRN.reals.stdlib.CMTMeasurableFunctions.

Locate CvMeasure.
Locate DominatedMeasureCvZero.
Locate DominatedConvergence.

Print Typing Flags.

Goal True. idtac "=== CvMeasure ===". exact I. Qed.
Print Assumptions CvMeasure.

Goal True. idtac "=== DominatedMeasureCvZero ===". exact I. Qed.
Print Assumptions DominatedMeasureCvZero.

Goal True. idtac "=== DominatedConvergence ===". exact I. Qed.
Print Assumptions DominatedConvergence.
