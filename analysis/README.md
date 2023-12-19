Analysis
========

Intra-procedural static analysis of MIR functions.

Each analysis compute a state for each program point:
* `DefinitelyInitializedAnalysis` computes the places that are definitely initialized. By enabling a flag, this analysis also considers "initialized" the places of `Copy` types after a *move* operation.
* `ReachingDefinitionAnalysis` computes for each local variable the set of assignments or function arguments from which the value of the local variable might come from.
* `MaybeBorrowedAnalysis` computes the places that are blocked due to a mutable reference or frozen due to a shared reference.
* `DefinitelyAccessibleAnalysis` computes the places that are are surely owned (i.e. can be borrowed by a mutable reference), accessible (i.e. can be borrowed by a shared reference) or locally shared (i.e. previously owned but now accessible only by the current thread).
* `FramingAnalysis` computes across each statement the places that are surely framed (e.g. owned by the client but not used by the statement).
* `DefinitelyUnreachableAnalysis` computes across each statement the places that are surely unreachable (i.e. mutably borrowed but unreachable due to reborrowing).
* `DefinitelyAllocatedAnalysis` computes which local variables are definitely allocated (i.e. after a `StorageLive` but before any `StorageDead`).
* `LocallySharedAnalysis` computes an under-approximation of the owned places (e.g. `x: Mutex<T>`) that have been shared (e.g. `let y = &x`) but are still local to the thread. Complements the `DefinitelyAccessibleAnalysis` analysis.
