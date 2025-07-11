# build\_tcl\_conns.awk

# Generates a single check\_conn command with all -connection flags and -view

BEGIN { 
FS = ","

"pwd" | getline cwd; close("pwd")

# 2) build full CSV path and base check_conn command
csv_file = cwd "/output_map.csv"
base_cmd = "check_conn -map " csv_file

# 3) count lines in the CSV (wc -l → "42 /path/to/output_map.csv")
"wc -l " csv_file | getline wc_out; close("wc -l " csv_file)
split(wc_out, parts, " ")
total_lines = parts[1] + 0

# 4) print the base command prefix
printf "%s ", base_cmd

}

# Skip header row if present

NR == 1 { next }

# For each line, emit the -connection flag; on last line, append -view

{ 
	sink = $2; 
	if (NR < total_lines) { 
		printf("-connection %s ", sink) 
	} else { 
		printf("-connection %s -view\n", sink) 
	} 
}

