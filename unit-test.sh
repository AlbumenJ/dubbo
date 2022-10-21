#!/bin/sh
# ----------------------------------------------------------------------------
# Licensed to the Apache Software Foundation (ASF) under one
# or more contributor license agreements.  See the NOTICE file
# distributed with this work for additional information
# regarding copyright ownership.  The ASF licenses this file
# to you under the Apache License, Version 2.0 (the
# "License"); you may not use this file except in compliance
# with the License.  You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.
# ----------------------------------------------------------------------------

mvn --batch-mode -no-transfer-progress dependency:go-offline

data=$(find . -name pom.xml | cut -c 3- | rev | cut -c 9- | rev | sort)

submodules=($data)

case_count=0
case_range=$CASE_RANGE
current_role=$CURRENT_ROLE

for (( i = 0; i < ${#submodules[@]}; i++ )); do
  if [ ${submodules[$i]} != "" ]; then
    if [ $case_count -eq $current_role ]; then
      echo "execute ${submodules[$i]} test cases"
      ./mvnw -pl ${submodules[$i]} -o --batch-mode --no-snapshot-updates -e --no-transfer-progress --fail-fast clean test verify -Pjacoco -DskipTests=false -DskipIntegrationTests=false -Dcheckstyle.skip=false -Dcheckstyle_unix.skip=false -Drat.skip=false -Dmaven.javadoc.skip=true -DembeddedZookeeperPath=$(pwd)/.tmp/zookeeper
      if [ $? -ne 0 ]; then
          exit $?
      fi
    fi
    case_count=$((case_count + 1))
    case_count=$((case_count % case_range))
  fi
done
