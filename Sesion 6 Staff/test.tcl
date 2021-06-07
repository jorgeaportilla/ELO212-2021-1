cd [file dirname [info script]]

# SESION NAME
puts "INGRESE NUMERO DE SESION (Ej. 4)"
gets stdin in
# Source in $SESION errors
if {[catch {source "Sesion${in}_params.tcl"} sesion_err]} {
    puts "ERROR AL LEER ARCHIVO Sesion${in}_params.tcl"
}

# Create Vivado Project with 
# ProjectName = $SESION_ELO212_TEST
# Target      = xc7a100tcsg324-1
# Path        = vivado/test
create_project -force ${SESION}_ELO212_Test -part xc7a100tcsg324-1 vivado/test
# Read all the SystemVerilog files in the directory
# Here it should be the testbenches for this $SESION Lab Experience
read_verilog -sv [glob *.sv]

# Set Simulation Runtime on 1[ms]
set_property -name "xsim.simulate.runtime" -value "1ms" -objects [get_filesets sim_1]

# Open a csv file to save the $STATUS on each $GROUP and its $ERRORS
set fp [open "notas_P${PARALELO}_${SESION}.csv" w+]
# Write first row in csv file
set CSV_HEADER "GRUPOS"
foreach ACT $ACTIVITIES {
    set CSV_HEADER "$CSV_HEADER;STATUS $ACT"
}
foreach ACT $ACTIVITIES {
    set CSV_HEADER "${CSV_HEADER};ERROR CODE $ACT"
}
puts $fp $CSV_HEADER


source test_utils.tcl
# Iterate over each $GROUP
for {set i $FIRST_GROUP} {$i <= $LAST_GROUP} {incr i} {
    GROUP_SIM $fp $i $PARALELO $SESION $ACTIVITIES [array get ACT_ERRORS]
}

# Write Errors and the associated code
puts $fp "\n\nERROR CODE"
foreach {code error_msg} [array get ACT_ERRORS] {
    puts $fp "[string map {, .} $code];$error_msg"
}

close $fp
close_project

