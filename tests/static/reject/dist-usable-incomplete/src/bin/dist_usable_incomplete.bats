#include "share/atspre_staload.hats"
#use array as A
#use arith as AR
staload Z = "zip/src/lib.sats"

(* A distance code that fits but is neither complete, single nor empty has no constructor: the fit alone is refused *)
prfn _fit_only {lengths:$A.cells} (fit: $Z.LENGTHS_FIT(lengths, 15)): $Z.DIST_USABLE(lengths) = $Z.DIST_USABLE_empty(fit, fit)

implement main0 () = ()
