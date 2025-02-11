#!/bin/bash

set -e

BASEDIR="$(realpath "$(dirname "$0")")"

CP_FILE="$BASEDIR/silver_classpath.txt"

if [ ! -f "$CP_FILE" ]; then
    (cd "$BASEDIR"; sbt "export runtime:dependencyClasspath" | tail -n1 > "$CP_FILE")
fi

exec java -cp "$(cat "$CP_FILE")" viper.silver.SilverRunner "$@"
