BEGIN {
	FS = ","

	#run the shell command "pwd", capture its stdout
    	"pwd" | getline cwd
    	close("pwd")
	filename = "output_map.csv"
	full_file = cwd "/" filename
	command = "check_conn -map " full_file
	"wc -l " full_file | getline qtd_lin
	close("wc -l " full_file)

	split(qtd_lin, parts, " ")
	qtd_lin = parts[1] + 0
}
NR == 1 {next}
{
	if (NR < qtd_lin){
		printf "-connection " $2 " "
	}else{
		printf "-connection " $2 " -view\n"
	}
}
