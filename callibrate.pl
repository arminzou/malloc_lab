#!/usr/bin/perl
use Getopt::Std;

# Calibrate throughput for malloc benchmarks depending on CPU type

sub usage
{
    printf STDERR "$_[0]\n";
    printf STDERR "Usage: $0 [-h] [-v] [-N REPS] [-e TOL] [-S] [-f]\n";
    printf STDERR "Options:\n";
    printf STDERR "   -h              Print this message\n";
    printf STDERR "   -v              Verbose mode\n";
    printf STDERR "   -N REPS         Run benchmark REPS times\n";
    printf STDERR "   -e TOL          Set tolerance for outlier detection\n";
    printf STDERR "   -S              Do NOT save results\n";
    printf STDERR "   -f              Prevent looking up of previous result\n";
    die "\n";	
}

$| = 1;       # Autoflush output on every print statement

getopts('hvN:e:Sf');

if ($opt_h) {
    &usage($ARGV[0]);
}

$verbose = 0;
if ($opt_v) {
    $verbose = 1;
}

# Parameters
# Where to get CPU information
$cpu_file = "/proc/cpuinfo";
$cpu_key = "model name";
# CPU info (extracted from file)
$cpu_info = "";

# Number of measurements
$N = 10;
if ($opt_N) {
    $N = $opt_N;
}

# Outlier deletion criterion
$outlier_threshold = 0.01;

if ($opt_e) {
    $outlier_threshold = $opt_e;
    if ($outlier_threshold >= 0.5) {
	die "Tolerance should be relative to 1.0, not 100\n";
    }
}

# Regular benchmark program
$benchprog = "./mdriver-ref";

$bench = "regular";

$save_results = 1;
if ($opt_S) {
    $save_results = 0;
}
$save_file = "./throughputs.txt";

$lookup_ok = 1;
if ($opt_f) {
    $lookup_ok = 0;
}


# Get the CPU info
$cmultistring = `grep '$cpu_key' $cpu_file` ||
    die "Couldn't get CPU information (key = '$cpu_key') from '$cpu_file'\n";

# Remove first entry
@cstrings = split "\n", $cmultistring;
$cstring = $cstrings[0];

# Remove all white space
$cstring =~ s/\s//g;

# Get data
@parts = split ":", $cstring;

$cpu_info = $parts[1];

if ($verbose > 0) {
    print "Got CPU info '$cpu_info'\n";
}

# See if can find data
if ((-e $save_file) && $lookup_ok == 1) {
    $rstring = `cat $save_file`;
    @entries = split "\n", $rstring;
    $found = 0;
    for $e (@entries) {
	($fcpu_info, $fbench, $favg) = split ":", $e;
	if ($fcpu_info eq $cpu_info && $fbench eq $bench) {
	    print "Callibration: CPU type $cpu_info, benchmark $fbench, throughput $favg\n";
	    exit(0);
	}
    }
}

# Run measurements
@values = ();

for ($i = 0; $i < $N; $i += 1) {
    $sval = `$benchprog` || die "Couldn't run $benchprog\n";
    chomp($sval);
    $val = $sval * 1.0;
    $values[$i] = $val;
    if ($verbose > 0) {
	print "$i\t$val\n";
    }
}

# Compute average of array.  Ignore elements with value 0.0
sub array_avg
{
    $n = $0;
    $sum = 0.0;
    for $v (@values) {
	if ($v > 0) {
	    $sum += $v;
	    $n += 1;
	}
    }
    $avg = $sum/$n;
    if ($verbose > 0) {
	print "Average $avg over $n elements\n";
    }
    sprintf("%.0f", $avg);
}



# Now start working on the result
$done = 0;
$avg = 0.0;

$startN = $N;

while (!$done) {
    $avg = &array_avg();
    $idx = 0;
    $done = 1;
    for $v (@values) {
	if ($v > 0 && $v < (1.0 - $outlier_threshold) * $avg) {
	    if ($verbose > 0) {
		print "Deleting\t$idx\t$v\n";
	    }
	    $values[$idx] = 0.0;
	    if ($N > $startN/2) {
		$N -= 1;
		$done = 0;
	    }
	}
	$idx += 1;
    }
}

if ($save_results == 0) {
    print "Callibration: CPU type $cpu_info, benchmark $bench, throughput $avg\n";
    exit(0);
}

@entries = ();

if (-e $save_file) {
    $rstring = `cat $save_file`;
    @entries = split "\n", $rstring;
    $idx = 0;
    $found = 0;
    for $e (@entries) {
	($fcpu_info, $fbench, $favg) = split ":", $e;
	if ($fcpu_info eq $cpu_info && $fbench eq $bench) {
	    if ($verbose > 0) {
		print "CPU:$cpu_info, benchmark:$bench.  Replacing average $favg with $avg\n";
	    }
	    $entries[$idx] = "$cpu_info:$bench:$avg";
	    $found = 1;
	}
	$idx += 1;
    }
    if ($found == 0) {
	$entries[$idx] = "$cpu_info:$bench:$avg";
	if ($verbose > 0) {
	    print "Appending entry $idx: $cpu_info:$bench:$avg\n";
	}
    }
} else {
    @entries = ("$cpu_info:$bench:$avg");
    if ($verbose > 0) {
	print "Created first entry: $cpu_info:$bench:$avg\n";
    }
}

open OUT, ">$save_file";
for $e (@entries) {
    print OUT "$e\n";
}
    
print "Callibration: CPU type $cpu_info, benchmark $bench, throughput $avg\n";

exit(0);
