open Printf
open List

type edge = (int*int)
type edge_list = edge array
type state = (int*edge_list)
type state_list = state array
type internals = {mutable name : string ; mutable contents : state_list}

let debug_out = ref stdout
let do_debug = ref false
let debug fmt =
  	let k result = if !do_debug then begin
				output_string !debug_out result ;
    	flush stdout ;
  	end in
  	Printf.kprintf k fmt

let (--) i j =
	let rec aux n acc =
		if n < i then acc else aux (n-1) (n :: acc)
	in aux j []

let choose_random lst = 
	let size = length lst in
	let choice = Random.int size in
	nth lst choice

class type finite_automata = object
		(* get the automata's name *)
		method get_name : string
		(* Retrieve a state *)
		method get_state : int -> state
		(* Get edges for a given state *)
		method get_edges : int -> edge_list
		(* Get an edge given its number within a state*)
		method get_edge : int -> int -> edge
		(* Return all states *)
		method show : state_list
		(* Run automata on input *)
		method run : int list -> int
		(* How many states are there? *)
		method num_states : int
		(* Huw many edges for a given state *)
		method num_edges : int -> int
		(* set the automata's name *)
		method set_name : string -> unit
		(* Set all states at once *)
		method set_states : state_list -> unit
		(* Set the value for a state *)
		method set_value : int -> int -> unit
		(* Set a given edge for a given state *)
		method set_state_edge : int -> int -> edge -> unit 
		(* Set the transition for an edge *)
		method set_edge_transition : int -> int -> int -> unit
		(* set the destination value for an edges *)
		method set_edge_destination : int -> int -> int -> unit
		(* Mutate seld *)
		method mutate : int list -> int list -> unit
		(* Build random fa *)
		method random_build : int -> int list -> int list -> unit
end

class amata : finite_automata = 

	(* Helper methods for random constructing states *)
	let random_edge_list pos_edges pos_states : edge_list  =
		let tmp_list = ref [] in
		iter (fun i -> if (Random.int 2) = 1 
						then tmp_list := i :: !tmp_list ) pos_edges ;
		if !tmp_list = [] then tmp_list := [choose_random pos_edges] ;
		Array.map (fun el -> (el, (choose_random pos_states))) (Array.of_list !tmp_list) in 
	let random_state pos_vals pos_edges pos_states : state = 
		let choice = choose_random pos_vals in
		(choice,(random_edge_list pos_edges pos_states)) in
	let random_state_list len pos_vals pos_edges pos_states : state_list =
		let lst = 0--len in
		Array.map (fun _ -> (random_state pos_vals pos_edges pos_states)) (Array.of_list lst) in

	let states = { name = "default"; contents = [|(0,[|(0,0)|])|] } in

	object(self)
		method get_name =
			states.name
		method set_name str = 
			states.name <- str 
		method set_states lst =
			states.contents <- lst 
		method get_edges state =
			let (s,es) = (self#get_state state) in es
		method get_edge state edge =
			let edges = self#get_edges state in
			edges.(edge)
		method num_states =
			Array.length states.contents
		method num_edges snum =
			let (v,edges) = (self#get_state snum) in
			Array.length edges
		method set_value snum va =
			let (o_va,o_el) = states.contents.(snum) in
			(states.contents).(snum) <- (va,o_el) ;
			()
		method set_state_edge state enum new_e =
			let (_,old_edges) = self#get_state state in
			try
				old_edges.(enum) <- new_e ;
			with
				| Invalid_argument x -> 
					printf "Attempting to change an edge out of bounds.\n" ;
		method set_edge_transition state edge value =
			let old_edges = self#get_edges state in
			let (t,d) = old_edges.(edge) in
			old_edges.(edge) <- (value,d) ;
		method set_edge_destination state edge value =
			let old_edges = self#get_edges state in
			let (t,d) = old_edges.(edge) in
			old_edges.(edge) <- (t,value) ;
		method get_state num =
			(states.contents).(num)
		method show =
			states.contents
		method random_build mx_st o_l o_v =
			let total_states = Random.int mx_st in
			let pos_states = 0 -- total_states in
			states.contents <- (random_state_list total_states o_v o_l pos_states) ; 
		method mutate o_l o_v =
			let choice = Random.int 3 in
			match choice with
			| 0 -> 
				debug "Deleting state\n" ;
				(* Delete state *)
				let len = self#num_states in
				if not (len <= 1) then
					let to_del_num = Random.int len in
					let new_arr = Array.make (len-1) (0,[|(0,0)|]) in
					let correc = ref 0 in
					for i = 0 to (len-2) do (* Len-1 is last in old, so one less than that *)
						if i = to_del_num then correc := 1 ;
						new_arr.(i) <- self#get_state (i + !correc) ;
					done ;
					let final_arr = Array.map
						(fun el ->
							let (v,edges) = el in
							let elist = Array.to_list edges in
							let newl = filter (fun x -> let (t,d) = x in not (d = len-1)) 
								elist in
							(v,(Array.of_list newl))) new_arr in 
					states.contents <- final_arr
				else
					self#mutate o_l o_v  
			| 1 -> 
					debug "Inserting state\n" ;
					(* insert state *)
					let len = self#num_states in
					let new_s = random_state o_l o_v (0--(len+1)) in
					let cpy = states.contents in
					Array.iteri
						(fun i el ->
							let (v,edges) = el in
							let add_transition = Random.int 2 in
							match add_transition with
							| 0 -> ()
							| 1 -> 
								let new_l = choose_random o_l in
								let next_e = [|(new_l,len+1)|] in
								let new_edge_list = Array.append edges next_e in
								states.contents.(i) <- (v,new_edge_list) ;
							| _ -> ()
							) states.contents ;
						states.contents <- Array.append cpy [|new_s|] ;
			| 2 ->
					(* change existing state *)
					let len = self#num_states in
					let to_change = Random.int len in
					let what_doing = Random.int 5 in
					debug  "Changing existing state(%d)\n" to_change ;
					match what_doing with
					| 0 -> 
							(* Change a value *)
							debug "Changing a value\n" ;
							let new_v = choose_random o_v in
							self#set_value to_change new_v 
					| 1 -> 
							(* Change a transition *)
							debug "Changing a transition\n" ;
							let new_t = choose_random o_l in
							let edge_pos = self#num_edges to_change in
							if edge_pos > 0 then
								let what_edge = Random.int edge_pos in
									debug "edge:%d,new:%d\n" what_edge new_t ;
									self#set_edge_transition to_change what_edge new_t
								else
									self#mutate o_l o_v 
					| 2 -> 
							(* Change a destination *)
							debug "Changing a destination:\n" ;
							let new_d = Random.int len in
							let edge_pos = self#num_edges to_change in
							if edge_pos > 0 then
								let what_edge = Random.int edge_pos in
									debug  "edge:%d,destination:%d\n" what_edge new_d;
									self#set_edge_destination to_change what_edge new_d
								else self#mutate o_l o_v  
					| 3 ->
							(* Add an edge *)
							debug "Adding an edge\n" ; 
							let (v,edges) = self#get_state to_change in
							let new_t = choose_random o_l in
							let new_d = Random.int len in
							let new_edges = Array.append edges [|(new_t,new_d)|] in
							states.contents.(to_change) <- (v,new_edges)
					| 4 ->
							(* Delete an edge *)
							debug "Deleting an edge\n" ;
							let (v,edges) = self#get_state to_change in
							let edge_pos = self#num_edges to_change in
							if edge_pos > 0 then
								let what_edge = (self#get_edge to_change (Random.int edge_pos)) in
								let edge_list = Array.to_list edges in
								let new_edges = Array.of_list (filter (fun x -> not (x = what_edge)) edge_list) in
									states.contents.(to_change) <- (v,new_edges)
								else
									self#mutate o_l o_v
					| _ -> ()
		method run (input_lst : int list) =
			let (ival,_) = self#get_state 0 in
			let value = ref ival in
			let state = ref 0 in
			let parse_input i = 
				(match (self#get_state !state) with
				| (new_val, elist) -> 
					try
						let (e,d) = find (fun p -> let (e,d) = p in i = e) 
							(Array.to_list elist) in
						value := new_val ;
						state := d ; ()
					with
						| Not_found -> () 
						| _ -> printf "Should be impossible?\n" ; () ) in
			iter parse_input input_lst ;
			!value
end

let my = new amata 
	
let main =
	let cool_list = [|(1,[|(2,3);(3,4)|])|] in
	my#set_states cool_list ;
	my#random_build 20 [1;2;3] [1;2;3;] ;
	let res = my#run [1;2;3] in
	List.iter (fun x -> my#mutate [1;2;3] [1;2;3]) (0--10000) ;

