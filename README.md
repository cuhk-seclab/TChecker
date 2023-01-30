# TChecker: Precise Static Inter-Procedural Analysis for Detecting Taint-Style Vulnerabilities in PHP Applications

TChecker is a static taint analysis tool for PHP applications. The key idea in TChecker is to iteratively construct call graph and precisely perform inter-procedural taint analysis. TChecker found 18 new vulnerabilities and two CVEs (CVE-2022-35212, CVE-2022-35213) were assigned.

## Prerequisite

~~~~~~{.sh}
Run php-cs-fixer (https://github.com/PHP-CS-Fixer/PHP-CS-Fixer) to fix the coding styles.
Run phpjoern (https://github.com/malteskoruppa/phpjoern) to generate the node file and edge file for a PHP application.
~~~~~~

## How to use

~~~~~~{.sh}
Run java -Xmx8G -cp "./bin:ApacheCommons/commons-cli-1.4/commons-cli-1.4.jar:ApacheCommons/commons-cli-1.4/commons-cli-1.4-sources.jar:ApacheCommons/commons-csv-1.8-bin/commons-csv-1.8/commons-csv-1.8.jar:ApacheCommons/commons-csv-1.8-bin/commons-csv-1.8/commons-csv-1.8-sources.jar:ApacheCommons/commons-lang3-3.10/commons-lang3-3.10.jar:ApacheCommons/commons-lang3-3.10/commons-lang3-3.10-sources.jar:ApacheCommons/json-20190722.jar"  tools.php.ast2cpg.Main TargetPHPApplication
Note that the call graph (call_graph.csv) is also generated in the current directory.
~~~~~~

## Author
Please contact chluo@cse.cuhk.edu.hk for any questions.