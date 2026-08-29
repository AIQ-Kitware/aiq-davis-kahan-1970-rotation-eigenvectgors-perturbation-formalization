# Alternative Davis--Kahan proofs

This directory contains proof-complete secondary implementations of results
whose canonical public versions live elsewhere. They are retained when they
provide a materially different dependency profile, a more explicit argument,
a finite-dimensional-only route, or a useful cherry-picking target.

Alternative modules are compiled but are not imported by `DavisKahan.lean`.
They must not serve as dependencies of canonical modules.

As the unbounded source theorem is promoted, existing bounded and finite proof
paths should remain available here through scoped wrappers or moved modules
when that improves ownership clarity. They should not be deleted merely
because a more general theorem exists: their weaker hypotheses and independent
arguments are valuable regression and reuse surfaces.
