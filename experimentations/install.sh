USAGE="$(basename $0) [-h] [-m] [-n] [-d] --\
  Installs environment variable for the Calendar,

where:
  -h, --help
      show this help text
  -m, --mac-local
      installs the variable and starts database (local exp -- mac environment)
  -n, --nix-local
      installs the variable (local exp -- nixos environment)
  -k, --kill
      kill all screens
  -d, --dist
      installs the project on heroku and google compute engine. This
      requires to set the variable `GG_COMP` with the ip of the google
      compute engine that stores the second database. `DB_USER` with
      the name of the second database. `DB_PASS` with the password of
      the second database."

case "$1" in
    -m|--mac-local)
        export CALENDAR_URL=http://localhost:3000
        export DATABASE_URL=postgres:///$(whoami)
        export DATABASE_URL2=postgres:///$(whoami)
        export DATABASE_HTTP2_PORT=3001
        export DATABASE_HTTP2=http://localhost:${DATABASE_HTTP2_PORT}
        screen -dm -S postgres postgres -D /usr/local/var/postgres
        screen -dm -S calendar-db2 node calendar-db2.js
        #screen -dm -S calendar-saas node calendar-saas.js
        screen -S calendar-saas node calendar-saas.js
        echo "Open your browser at ${CALENDAR_URL}"
        ;;

    -n|--nix-local)
        export CALENDAR_URL=http://localhost:3000
        export DATABASE_URL=postgres://$(whoami):passwd@localhost/$(whoami)
        export DATABASE_URL2=postgres://$(whoami):passwd@localhost/$(whoami)
        export DATABASE_HTTP2_PORT=3001
        export DATABASE_HTTP2=http://localhost:${DATABASE_HTTP2_PORT}
        screen -dm -S calendar-db2 node calendar-db2.js
        screen -dm -S calendar-saas node calendar-saas.js
        echo "Open your browser at ${CALENDAR_URL}"
        ;;

    -d|--dist)
        source dist-var.private
        heroku config:set DATABASE_URL2=postgres://${DB_USER}:${DB_PASS}@${GG_COMP}:5432/${DB_USER}
        heroku config:set DATABASE_HTTP2=http://${GG_COMP}
        screen -dm -S calendar-saas heroku logs --tail
        echo "Remember 1: set number of dyno to 1 in heroku"
        echo "> heroku ps:scale web=1"
        echo "Remember 2: start google cloud platform instance"
        echo "Also start calendar-db2.js as root"
        echo "Remember 3: launch app without https"
        echo "http://calendar-exp.herokuapp.com"
        echo "Remember 4: If your are on Chromium, it complains"
        echo "about some security origin (since I don't go with https" 
        echo "quick prototyping)"
        echo "Launch chromium with"
        echo "./Chromium --user-data-dir=/tmp/foo --ignore-certificate-errors --unsafely-treat-insecure-origin-as-secure=http://calendar-exp.herokuapp.com"
        ;;

    -k|--kill)
        screen -ls | grep Detached | cut -d. -f1 | awk '{print $1}' | xargs kill
        pkill postgres
        pkill node
        ;;

    -h|--help|*)
        echo "${USAGE}"
        exit
        ;;
esac
