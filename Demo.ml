(* Michaël PÉRIN, Verimag / Université Grenoble-Alpes, Février 2017 
 *
 * Part of the project TURING MACHINES FOR REAL
 *
 * Runs of Turing Machines
 *
 *)


open Symbol
open Alphabet
open Band
open Transition
open Turing_Machine
open Configuration
open Execution
  
let (incr_decr: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [B;Z;U;D] in
	let band1 = Band.make alphabet [U;U;Z;U] in
	  let tm = Turing_Machine.sequence [ Run Turing_Machine.incr ; Run Turing_Machine.left_most ; Run Turing_Machine.decr ] in
	    let cfg = Configuration.make tm [ band1 ] in
	      Execution.log_run cfg 


let (incr: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [B;Z;U;D] in
	let band1 = Band.make alphabet [U;U;Z;U] in
	  let cfg = Configuration.make Turing_Machine.incr [ band1 ] in
	    Execution.log_run cfg 
	      

let (decr1: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [B;U;Z;D] in
	let band1 = Band.make alphabet [Z;Z;Z;U] in
	  let cfg = Configuration.make Turing_Machine.decr [ band1 ] in
	    Execution.log_run cfg 

let (decr2: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [B;U;Z;D] in
	let band1 = Band.make alphabet [Z;Z;Z;U;U] in
	  let cfg = Configuration.make Turing_Machine.decr [ band1 ] in
	    Execution.log_run cfg 
	      

let (gen_dup: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [B;Z;U;D] in
	let dup = Turing_Machine.generic_dup alphabet.symbols in
	  let band1 = Band.make alphabet [U;Z;Z;U] in
	    let cfg = Configuration.make dup [ band1 ] in
	      Execution.log_run cfg 

let (gen_copy: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [B;U;Z] in
	let copy = Turing_Machine.generic_copy alphabet.symbols in
	  let band1 = Band.make alphabet [Z;U;U;Z] 
	  and band2 = Band.make alphabet [] in
	    let cfg = Configuration.make copy [ band1 ; band2 ] in
	      Execution.log_run cfg 

	      
let (gen_reverse: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [B;U;Z] in
	let reverse = Turing_Machine.generic_reverse alphabet.symbols in	
	  let band1 = Band.make alphabet [U;Z;U;U;Z;Z] 
	  and band2 = Band.make alphabet [] in
	    let cfg = Configuration.make reverse [ band1 ; band2 ] in
	      Execution.log_run cfg 


let (gen_swap: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [B;U;Z] in
	let swap = Turing_Machine.generic_swap alphabet.symbols in	
	  let band1 = Band.make alphabet [U;Z;U;U;Z;Z] in
	    let cfg = Configuration.make swap [ band1 ] in
	      Execution.log_run cfg 

let (xor: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [B;Z;U] in
	let band1 = Band.make alphabet [U;Z;U;U;Z;Z] 
	and band2 = Band.make alphabet [U;Z;U;U;Z;Z] in
	  let cfg = Configuration.make Turing_Machine.xor [ band1 ; band2 ] in
	    Execution.log_run cfg
		

let (busy_beaver: Turing_Machine.t -> Configuration.t) = fun bb ->
      let alphabet = Alphabet.binary in
	let band = Band.make alphabet [] in
	  let cfg = Configuration.make bb [ band ] in
	    Execution.log_run cfg 

let (c_p: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [B;Z;U;O] in
	let band1 = Band.make alphabet [O;Z;C;O;C] 
	and band2 = Band.make alphabet [B;B;B;B;B] in
	  let cfg = Configuration.make Turing_Machine.check_parenthesis [ band1 ; band2 ] in
	    Execution.log_run cfg



let (test: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [B;Z;U;O;S;D;L] in
	let band1 = Band.make alphabet [L;U;Z;O;U;U;O;U;C;C;O;C] 
	and band2 = Band.make alphabet [B;B;B;B;B] 
	and band3 = Band.make alphabet [B;B;B;B;B] in 
	  let cfg = Configuration.make Turing_Machine.real_one [ band1 ; band2 ; band3] in
	    Execution.log_run cfg

let (sub: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [Z;U;O;S;L;X;C;S] in
	let substitution = Turing_Machine.substitution alphabet.symbols in
	let band1 = Band.make alphabet (*[O;L;X;Z;Z;O;L;X;U;Z;O;L;X;Z;U;O;X;Z;Z;X;Z;Z;C;C;C;C;O;X;U;Z;C;O;X;Z;U;C;O;X;U;U;C]*)
	[O;L;X;Z;Z;Z;Z;O;L;X;Z;Z;Z;U;O;L;X;Z;Z;U;Z;O;X;Z;Z;U;Z;O;X;Z;Z;Z;Z;C;X;Z;Z;Z;U;C;C;C;C;O;L;X;U;U;U;U;O;Z;U;U;Z;C;C;O;X;U;U;U;Z;C;O;X;U;U;Z;Z;C]
	and band2 = Band.make alphabet [B;B;B;B;B;B;B;B;B;B;B;B;B;B;B;B;B;B;B] 
	and band3 = Band.make alphabet [B;B;B;B;B;B;B;B;B;B;B;B;B;B;B;B;B;B;B]
	and band4 = Band.make alphabet [B;B;B;B;B;B;B;B;B;B;B;B;B;B;B;B;B;B;B] in 
	  let cfg = Configuration.make substitution [ band1 ; band2 ; band3 ; band4] in
	    Execution.log_run cfg

let (app: unit -> Configuration.t) = fun () ->
      let alphabet = Alphabet.make [Z;U;O;D;L;X;C] in
	let application = Turing_Machine.copyTerme alphabet.symbols in
	let band1 = Band.make alphabet [O;L;X;Z;L;X;U;O;Z;U;C;C;O;X;U;U;U;C] 
	and band2 = Band.make alphabet [B;B;B;B;B] 
	and band3 = Band.make alphabet [B;B;B;B;B] in 
	  let cfg = Configuration.make application [ band1 ; band2 ; band3] in
	    Execution.log_run cfg


(* DEMO *)
	        
let (demo: unit -> unit) = fun () ->
      begin
	print_string "\n\n* DEMO * Demo.ml:\n\n" ;
	List.iter (fun _ -> ())
	  [ incr ()  ;
	    decr1 () ;
	    decr2 () ;    
	    incr_decr () ;
	    gen_dup () ;
	    gen_copy () ;    
	    gen_reverse () ;
	    gen_swap () ;
	    xor () ;
	    busy_beaver Turing_Machine.bb4 ;
	    c_p();
	    app();
 	    sub();
	
	    (*c_ps();*)
	    test();	
	    
	    
	    
           (* 
	    * /!\  TERMINATING BUT EXTREMLY LONG COMPUTATIONS ... The sun will be dead before the end of BB6.
	    *
	      busy_beaver Turing_Machine.bb5 ;    
	      busy_beaver Turing_Machine.bb6 ;    
	    *)
	  ]
      end

