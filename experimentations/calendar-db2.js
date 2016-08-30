// WebServer stuff
const express = require('express');
const app = express();

// Database stuff
const pg = require('pg');
const DB_URL = process.env.DATABASE_URL2;

function query (dbUrl, sql) {
  return new Promise((resolve, reject) => {
    // `done` is for releasing the client from the pg pool
    pg.connect(dbUrl, (err, client, done) => {
      // Handle error on pg
      const handleError = function (err) {
        if (!err) { return false; }
        if (client) { done(client); }

        reject(err);

        return true;
      };

      // Call the query on pg
      if (!handleError(err)) {
        client.query(sql, (err, res) => {
          if (!handleError(err)) {
            done();
            resolve(res.rows);
          }
        });
      }
    });
  });
}

app.set('port', (process.env.DATABASE_HTTP2_PORT || 80));

app.use(function(req, res, next) {
  res.header("Access-Control-Allow-Origin", "*");
  res.header("Access-Control-Allow-Headers",
             "Origin, X-Requested-With, Content-Type, Accept");
  next();
});

app.get('/exec/:query', (req, res) => {
  query(DB_URL, req.params.query)
    .then(rows => res.type('json').send(rows))
    .catch(err => console.error(err));
});


const server = app.listen(app.get('port'), function() {
  const host = server.address().address;
  const port = server.address().port;

  console.log('Example app listening at http://%s:%s', host, port);
});
