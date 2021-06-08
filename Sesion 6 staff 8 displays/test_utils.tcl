##### --------- COMMAND FOR GROUP SIMULATION---------- #####
proc GROUP_SIM {FILE GN PARALELO SESION ACTIVITIES ACT_ERRORS} {
    array set ACT_ERRORS_SIM $ACT_ERRORS

    set GN [if {$GN < 10} {list "0$GN"} {list "$GN"}] ; # Define Group Number. It should add a 0 if the Group Number < 10
    set GROUP "G${PARALELO}${GN}"                     ; # Group Identification 
    set DIRECTORY "${GROUP}_${SESION}"                ; # Directory Name 
    set STATUS ""                                     ; # STATUS Initialization
    set ERRORS ""                                     ; # ERRORS Initialization 

    # Iterate over Activities in the Laboratory Experience
    foreach ACT $ACTIVITIES {
        # Set top module for simulation
	set_property -name "top" -value "test_$ACT" -objects [get_filesets sim_1]
        # Read the SystemVerilog files. 
	set err_read [catch {read_verilog -sv [glob $DIRECTORY/$ACT/*.sv]} err_read_msg]
        if {$err_read} {
            ##### --------- DIRECTORY NOT FOUND---------- #####
            set STATUS "$STATUS;FAIL"
            set ERRORS "$ERRORS;$ACT NOT FOUND"
        } else {
            ##### --------- SOURCES READ SUCCEED ---------- #####
	    update_compile_order -fileset sources_1
	    # Launch simulation and save last message
	    catch {
	    	launch_simulation
	    } error_message
	    # Check ERROR word if simulation fails before it finishes
	    if {[string match ERROR* $error_message]} {
                ##### --------- SIMULATION THROWS ERROR ---------- #####
	    	set STATUS "$STATUS;FAIL"
	    	set ERRORS "$ERRORS;SIMULATION ERROR"
	    } else {
                ##### --------- SIMULATION SUCCEED ---------- #####
                # Get pass variable testbench's value
	    	set message [get_value -radix unsigned pass]
	    
	    	if {$message} {
                    ##### --------- PASS ---------- #####
	    	    set STATUS "$STATUS;PASS"
	    	    set ERRORS "$ERRORS;"
	    	} else {
                    ##### --------- FAIL ---------- #####
                    set error_msg [get_value -radix unsigned error_code]
	    	    set STATUS "$STATUS;FAIL"
	    	    set ERRORS "$ERRORS;$error_msg"
	    	}
	    	close_sim
	    }
        }
    }
    puts $FILE $GROUP$STATUS$ERRORS
	
	

    foreach ACT $ACTIVITIES {
		set err_read [catch {remove_files [glob $DIRECTORY/$ACT/*.sv]} err_read_msg]
		if {$err_read} {
			puts "${ACT}_NOT_FOUND"
		}
		
    }
}
