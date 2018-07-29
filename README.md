# TimSort
Verified C implementation of TimSort using Isabelle/HOL

The "*.thy" files are Simpl specification and proof of Timsort in Isabelle/HOL. 

how to build these theories:<br>
&ensp;&ensp; run `build -D .`

TimSortLemma.thy<br>
&ensp;&ensp;Relevant lemmas for proving the specification.
  
TimSortProc.thy<br>
&ensp;&ensp;Definition of procedures.
  
GallopA.thy<br>
&ensp;&ensp;Specifications for procedure `gallop_left`, `gallop_right`,`merge_lo` and `merge_hi`
  
TimSort.thy<br>
&ensp;&ensp;Specifications for the other procedures
  

The "Simpl" directory contains the Simpl lib of Isabelle/HOL. 

The "C" directory is the generated C code of Timsort including a set of random test cases. 
