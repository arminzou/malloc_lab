#!/usr/bin/perl
use Getopt::Std;


##############################################################################
#
# This program is used to test a malloclab submission for correctness and
# performance using mdriver.
#
##############################################################################

sub usage 
{
    printf STDERR "$_[0]\n";
    printf STDERR "Usage: $0 [-h] [-s SECONDS]\n";
    printf STDERR "Options:\n";
    printf STDERR "  -h              Print this message\n";
    printf STDERR "  -s SECONDS      Set driver timeout\n";
    die "\n" ;
}

# Generic setting
$| = 1;      # Autoflush output on every print statement

# Settings
# Driver timeout
$timeout = 180;

getopts('hs:');

if ($opt_h) {
    usage($ARGV[0]);
}

if ($opt_s) {
    $timeout = $opt_s;
}

$callibration_flags = "";
$driver_flags = "";

# Run callibration program
$callibration_prog = "./callibrate.pl";

if (!-e $callibration_prog) {
    die "Cannot find callibration program $callibration_prog\n";
}

system("$callibration_prog $callibration_flags");

$driver_prog = "./mdriver";

if (!-e $driver_prog) {
    die "Cannot find driver program '$driver_prog'\n";
}

print "Running $driver_prog -s $timeout $driver_flags\n";

$dstring = `$driver_prog -A -s $timeout $driver_flags 2>&1` ||
    die "Couldn't run driver $driver_prog\n";

$found_autograde = 0;
$prefix = "";
$score = 0;
$mid = "";
@fields = ();
$suffix = "";

# Extract the autograde JSON from the driver output
for $line (split "\n", $dstring) {
    if ($line =~ /Autograded Score/) {
        $found_autograde = 1;
        $line =~ /^([^0-9]*)([0-9\.]+)([^0-9]*)\[(.*)\](.*)$/;
        $prefix = $1;
        $score = $2;
        $mid = $3;
        $list = $4;
        @fields = split ",[\s]*", $list;
        $suffix = $5;
    } else {
        print "$line\n";
    }
        
}

if (!$found_autograde) {
    print "Driver $driver_prog failed.  Exiting\n";
    exit(0);
}

$nlist = join(', ', @fields);
print $prefix . $score . $mid . "[$nlist]" . $suffix . "\n";
