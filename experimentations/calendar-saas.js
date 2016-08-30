// WebServer stuff
const express = require('express');
const app = express();
const timeout = require('connect-timeout');

// Crypto stuff
const crypto = require('crypto');
const SKEY = 'passwd';

// Database stuff
// pg_dump $(whoami) > db.out ; ll -h db.out
// clear: 5.6 Mo
const pg = require('pg');
const DB1_URL = process.env.DATABASE_URL;
const DB2_URL = process.env.DATABASE_URL2;
const DB2_HTTP = process.env.DATABASE_HTTP2;

// const NB_MEETINGS = 2500;
const NB_MEETINGS = 100;
// const LIMIT = 2500;
const LIMIT = 5;


// Utils stuff
const Lazy = require('lazy.js');


// Utils functions
const Utils = {
  // :: date&time → date
  truncateDate: function (date) {
    return new Date(date.getFullYear(), date.getMonth(), date.getDate());
  },

  seqPromises: function (promises) {
    return Lazy(promises)
    .reduce((z, p) => z.then(_ => p()), Promise.resolve());
  },

  crypto: {
    // ;; The encryption algorithm.
    //
    // Note: Going with ecb is not really secure since the encryption
    // is not randomized with an `iv` (like in cbc). But this makes
    // easy to test homomorphic equality. Otherwise you can fix the
    // `iv` so that you get the deterministic encryption back. There
    // we choose to fix the `iv` since webcrypto doesn't implement ecb
    // scheme.
    //
    // _algo : 'aes-256-ecb', // Key size 32, iv size: 0
    // _algo : 'aes-128-ecb', // Key size 16, iv size: 0
    _algo: 'aes-256-cbc', // Key size 32, iv size: 16.


    // ;; The Initialization vector.
    //
    // A fixed-size input to aes that makes the encryption random (i.e,:
    // repeated usage of the scheme under the same key does not allow an
    // attacker to infer relationships between segments of the encrypted
    // message).
    //
    // The size is 16 bytes as the number of bytes in a aes block.
    // Here each byte has been encoded as two hexadecimal character.
    //
    // Note: The `iv` should be changed after each encryption. `iv`,
    // just like the salt are public values so you can store it in the
    // database without any risk. Once again, there we are interested
    // in a poor Equal Homorphic Property, so we fix the value to be
    // deterministic during encryption.
    //
    // aes-*-ecb doesn't require `iv` this makes it less secure but
    // deterministic. aes-*-cbc requires an `iv` 16 bytes long.
    //
    _iv: new Buffer('380d853e8dd4941152ab94bc60aee3cb', 'hex'),
    // _iv : crypto.randomBytes(16),
    // _iv : crypto.randomBytes(0),

    // ;; The salt for enhanced key.
    //
    // Note: The salt should be change every time. The sault, just
    // like the `iv` are public values so you can store it in the
    // database without any risk. Once again, there we are interested
    // in a poor Equal Homorphic Property, so we fix the value to be
    // deterministic during encryption.
    _salt : 'the-salt',

    // :: string → {key: buffer, salt: string}
    //
    // Returns the enhanced key for encryption/decryption.
    //
    // We use pbkdf2 for deriving an enhanced key and prevent from
    // brute force attack by increasing the time it takes to test each
    // possible key. The number of iteration is 100 and the hash is a
    // sha256.
    //
    // See key stretching.
    // https://en.wikipedia.org/wiki/Key_stretching
    //
    // The key is returned with its salt in a string.
    enhanceKey: function (passwd) {
      return {
        key: crypto.pbkdf2Sync(
          passwd, Utils.crypto._salt, 100, 32, 'sha256'),
        salt: Utils.crypto._salt
      };
    },

    // :: (string, string) → {value: hex string, salt: string, iv: hex string}
    //
    // Encrypts an UTF-8 string. This returns a cipher object. Strings
    // are hexadecimal representation of the resulted buffers except
    // for the salt that is a normal String.
    encrypt: function (passwd, str) {
      // Generate the key
      const enhancedKey = Utils.crypto.enhanceKey(passwd);

      // Make the object responsible for the encryption.
      const cipher = crypto.createCipheriv(Utils.crypto._algo,
                                           enhancedKey.key,
                                           Utils.crypto._iv);

      // Encrypts
      var encrypted = cipher.update(str, 'utf8', 'hex');
      encrypted += cipher.final('hex');

      return {
        value: encrypted,
        salt: enhancedKey.salt,
        iv: Utils.crypto._iv.toString('hex')
      };
    },

    // :: (string, {value: hex string, salt: string, iv: hex string}) → string
    //
    // Decrypts a cipher object
    decrypt: function (passwd, cipher) {
      // Get back key and iv
      const enhancedKey =
              crypto.pbkdf2Sync(passwd, cipher.salt, 100, 32, 'sha256');
      const iv = new Buffer(cipher.iv, 'hex');

      // Make the object responsible for the decryption
      const decipher = crypto.createDecipheriv(Utils.crypto._algo,
                                               enhancedKey,
                                               iv);

      // Decrypts
      var decrypted = decipher.update(cipher.value, 'hex', 'utf8');
      decrypted += decipher.final('utf8');

      return decrypted;
    },

    // :: (string, meeting) → {value: hex string, salt: string, iv: hex string}
    //
    // Encrypts a meeting. The returned strings are hexadecimal
    // representation of the resulted buffers except for salt that is
    // a normal String.
    encryptMeeting: function (passwd, meeting) {
      return Utils.crypto.encrypt(passwd, JSON.stringify(meeting));
    },

    // :: (string, {meeting: hex string, salt: string, iv: hex string})
    //      → meeting
    //
    // Decrypts a meeting
    decryptMeeting: function (passwd, encMeeting) {
      return JSON.parse(decrypt(passwd, encMeeting));
    }
  }
};

// -- Some tests on crypto lib
// var testSEnc =  Utils.crypto.encrypt('passwd', 'lala');
// console.log(testSEnc);
// console.log(Utils.crypto.encrypt('passwd', 'lala'));
// console.log(Utils.crypto.decrypt('passwd', testSEnc));

// var testMEnc = Utils.crypto.encryptMeeting('passwd', {
//   date: new Date(),
//   name: "Bob",
//   address: "Work"
// });
// console.log(testMEnc);
// console.log(Utils.crypto.encrypt('passwd', 'lala'));
// console.log(Utils.crypto.decrypt('passwd', testMEnc));


// App
const Calendar = {
  // ---------------------------------------------------- namespace: clear
  clear: {
    // Drop the clear data in the database
    drop: function() {
      console.log("clear#drop");

      return Calendar.q(DB1_URL, "DROP SCHEMA IF EXISTS clear CASCADE;");
    },

    // Install the database
    install: function (size) {
      console.log("clear#install");

      // SQL request that insert a new meeting for Alice
      const mk$insertMeeting = function (meeting) {
        return "INSERT INTO clear.meetings (userId, date, name, address)" +
          `values('Alice', '${meeting.date.toISOString()}', ` +
          `'${meeting.name}', '${meeting.address}');`;
      };

      // The meeting to add
      const $insertMeeting = mk$insertMeeting({
        date: new Date(),
        name: "Bob",
        address: "Work"
      });

      return Calendar
        .q(DB1_URL, "CREATE SCHEMA clear;")
        .then(_ => Calendar.q(DB1_URL,
                              "CREATE TABLE clear.meetings (" +
                              "  userid  varchar(10)," +
                              "  date    timestamp with time zone," +
                              "  name    varchar(10)," +
                              "  address text" +
                              ");"))
        .then(_ => Calendar.q(DB1_URL, Lazy
                              .generate(_ => $insertMeeting)
                              .take(size)
                              .join("")));
    },

    // The places request
    places: function () {
      console.log("clear#places");

      return Calendar
        .q(DB1_URL,
           "SELECT DISTINCT name, address " +
           "FROM clear.meetings " +
           "WHERE userid = 'Alice'" +
           "AND name LIKE 'B%';");
    },

    // meetings next week
    // The meetings request: try to put all things together. We cannot
    // apply the left first strat since date is in the result and we
    // have to request right frag.
    meetingsWithBob: function () {
      console.log("clear#meetingsWithBob");

      var res = {};
      return Calendar
        .q(DB1_URL,
           "SELECT date::date, COUNT(*) FROM clear.meetings " +
           "WHERE userid = 'Alice' " +
           "AND name LIKE 'Bob' " +
           "AND address LIKE 'Work' " +
           "AND (date::date - CURRENT_DATE) BETWEEN 0 AND 7 " +
           "GROUP BY date::date;")
        .then(rows => rows.map(r => res[r.date] = +r.count))
        .then(_ => Promise.resolve(res));
    },

    meetings: function (limit) {
      console.log("clear#meetings");

      return Calendar
        .q(DB1_URL,
           "SELECT date, name, address FROM clear.meetings " +
           "WHERE userid = 'Alice' " +
           `LIMIT ${limit} OFFSET 0;`);
    }
  },

  // ----------------------------------------------------- namespace: sym
  sym: {
    drop: function() {
      console.log("sym#drop");

      return Calendar.q(DB1_URL, "DROP SCHEMA IF EXISTS sym CASCADE;");
    },

    // Install the database
    install: function (size) {
      console.log("sym#install");

      const mk$insertMeeting = function (meeting) {
        return "INSERT INTO sym.meetings (userId, meeting) " +
          `values('Alice', '${JSON.stringify(meeting)}');`;
      };

      // The meeting to add, protected with aes 256
      const $insertMeeting = mk$insertMeeting(
        Utils.crypto.encryptMeeting(SKEY, {
          date: new Date(),
          name: "Bob",
          address: "Work"
        }));

      return Calendar
        .q(DB1_URL, "CREATE SCHEMA sym;")
        .then(_ => Calendar.q(DB1_URL,
                              "CREATE TABLE sym.meetings (" +
                              "  userId  varchar(10)," +
                              "  meeting text" +
                              ");"))
        .then(_ => Calendar.q(DB1_URL, Lazy
                              .generate(_ => $insertMeeting)
                              .take(size)
                              .join("")));
    },

    places: function () {
      console.log("sym#places");

      return Calendar.q(DB1_URL,
                        "SELECT meeting FROM sym.meetings " +
                        "WHERE userid = 'Alice';");
    },

    // The meetings request
    // Returns all meeting inside the database
    meetingsWithBob: function () {
      console.log("sym#meetingsWithBob");

      return Calendar.q(DB1_URL,
                        "SELECT meeting FROM sym.meetings " +
                        "WHERE userid = 'Alice';");
    },

    meetings: function (limit) {
      console.log("sym#meetings");

      return Calendar
        .q(DB1_URL,
           "SELECT meeting FROM sym.meetings " +
           "WHERE userid = 'Alice' " +
           `LIMIT ${limit} OFFSET 0;`);
    }
  },

  // ----------------------------------------------------- namespace: frag
  frag: {
    drop: function() {
      console.log("frag#drop");

      return Promise
        .all([
          Calendar.q(DB2_URL,
                     "DROP SCHEMA IF EXISTS leftFrag CASCADE;"),
          Calendar.q(DB1_URL,
                     "DROP SCHEMA IF EXISTS rightFrag CASCADE;")]);
    },

    install: function (size) {
      console.log("frag#install");

      // SQL request that insert a new meeting for Alice
      const mk$insertMeeting = function (meeting) {
        const encName = Utils.crypto.encrypt(SKEY, meeting.name);

        const $leftMeeting =
                "INSERT INTO leftFrag.meetings " +
                "(userId, date, name_enc) values ('Alice', " +
                `'${meeting.date.toISOString()}', ` +
                `'${JSON.stringify(encName)}');`;

        const $rightMeeting =
                "INSERT INTO rightFrag.meetings " +
                "(userId, name_key, address) values ('Alice', " +
                `'${SKEY}', '${meeting.address}');`;

        return {left: $leftMeeting, right: $rightMeeting};
      };

      // The meeting to add
      const $insertMeeting = mk$insertMeeting({
        date: new Date(),
        name: "Bob",
        address: "Work"
      });

      // Initialize the database
      const leftPromise =
              Calendar.q(DB2_URL, "CREATE SCHEMA leftFrag;")
              .then(_ => Calendar.q(DB2_URL,
                                    "CREATE TABLE leftFrag.meetings (" +
                                    "  userid   varchar(10)," +
                                    "  date     timestamp with time zone," +
                                    "  name_enc text," +
                                    "  id       serial" +
                                    ");"))
              .then(_ => Calendar.q(DB2_URL, Lazy
                                    .generate(_ => $insertMeeting.left)
                                    .take(size)
                                    .join("")));

      const rightPromise =
              Calendar.q(DB1_URL, "CREATE SCHEMA rightFrag;")
              .then(_ => Calendar.q(DB1_URL,
                                    "CREATE TABLE rightFrag.meetings (" +
                                    "  userid   varchar(10)," +
                                    "  name_key text," +
                                    "  address  text," +
                                    "  id       serial" +
                                    ");"))
              .then(_ => Calendar.q(DB1_URL, Lazy
                                    .generate(_ => $insertMeeting.right)
                                    .take(size)
                                    .join("")));

      return Promise.all([leftPromise, rightPromise]);
    },

    places: function () {
      console.log("frag#places");

      const leftPromise = Calendar
              .q(DB2_URL,
                 "SELECT name_enc, id " +
                 "FROM leftFrag.meetings " +
                 "WHERE userid = 'Alice';");

      const rightPromise = Calendar
              .q(DB1_URL,
                 "SELECT name_key, address, id " +
                 "FROM rightFrag.meetings " +
                 "WHERE userid = 'Alice';");

      return Promise
        .all([leftPromise, rightPromise])
        .then(rows => {
          const leftRows = Lazy(rows[0]).sortBy('id');
          const rightRows = Lazy(rows[1]).sortBy('id').toArray();

          return leftRows.zip(rightRows)
            .map(lr => ({
              name: Utils.crypto.decrypt(
                lr[1].name_key,
                JSON.parse(lr[0].name_enc)),
              address: lr[1].address
            }))
            // I do the distinct at app level since I have to join
            // both frags to get the correct name value.
            .uniq(meet => meet.name+meet.address)
            .filter(meet => meet.name.startsWith('B'))
            .toArray();
        });
    },

    meetingsWithBob: function () {
      console.log("frag#meetingsWithBob");

      const leftPromise = Calendar
              .q(DB2_URL,
                 "SELECT date::date, name_enc, id " +
                 "FROM leftFrag.meetings " +
                 "WHERE userid = 'Alice' " +
                 "AND (date::date - CURRENT_DATE) BETWEEN 0 and 7");

      const rightPromise = Calendar
              .q(DB1_URL,
                 "SELECT name_key, id FROM rightFrag.meetings " +
                 "WHERE userid = 'Alice' " +
                 "AND address LIKE 'Work'");

      var res = {};
      return Promise
        .all([leftPromise, rightPromise])
        .then(rows => {
          const leftRows = Lazy(rows[0])
                  .indexBy('id', lr => lr)
                  .toObject();
          const rightRows = Lazy(rows[1]);

          return rightRows
            .filter(rr => leftRows.hasOwnProperty(rr.id))
            .map(rr => {
              const lr = leftRows[rr.id];

              return {
                date: lr.date,
                name: Utils.crypto.decrypt(
                  rr.name_key,
                  JSON.parse(lr.name_enc))
              };
            })
            .filter(meet => meet.name === 'Bob')
            .countBy(meet => Utils.truncateDate(meet.date))
            .toArray()
            .map(r => res[r[0]] = +r[1]);
        })
        .then(_ => res);
    },

    meetings: function (limit) {
      console.log("frag#meetings");

      const leftPromise = Calendar
              .q(DB2_URL,
                 "SELECT date, name_enc, id " +
                 "FROM leftFrag.meetings " +
                 `LIMIT ${limit} OFFSET 0;`);

      const rightPromise = Calendar
              .q(DB1_URL,
                 "SELECT name_key, address, id " +
                 "FROM rightFrag.meetings " +
                 `LIMIT ${limit} OFFSET 0;`);

      return Promise
        .all([leftPromise, rightPromise])
        .then(rows => {
          const leftRows = Lazy(rows[0]).sortBy('id');
          const rightRows = Lazy(rows[1]).sortBy('id').toArray();

          return leftRows.zip(rightRows)
            .map(lr => ({
              date: lr[0].date,
              name: Utils.crypto.decrypt(
                lr[1].name_key,
                JSON.parse(lr[0].name_enc)),
              address: lr[1].address
            }))
            .toArray();
        });
    }
  },

  // ----------------------------------------------------- namespace: phant
  phant: {
    drop: function() {
      console.log("phant#drop");

      return Promise.all([
        Calendar.q(DB2_URL,
                   "DROP SCHEMA IF EXISTS leftPhant CASCADE;"),
        Calendar.q(DB1_URL,
                   "DROP SCHEMA IF EXISTS rightPhant CASCADE;"),
      ]);
    },

    install: function (size) {
      console.log("phant#install");

      // SQL request that insert a new meeting for Alice
      const mk$insertMeeting = function (meeting) {
        const encName = Utils.crypto.encrypt(SKEY, meeting.name);

        const $leftMeeting =
                "INSERT INTO leftPhant.meetings " +
                "(userId, date) values ('Alice', " +
                `'${meeting.date.toISOString()}');`;

        const $rightMeeting =
                "INSERT INTO rightPhant.meetings " +
                "(userId, name, address) values ('Alice', " +
                `'${JSON.stringify(encName)}', '${meeting.address}');`;

        return {left: $leftMeeting, right: $rightMeeting};
      };


      // The meeting to add
      const $insertMeeting = mk$insertMeeting({
        date: new Date(),
        name: "Bob",
        address: "Work"
      });

      // Initialize the database
      const rightPromise = Calendar.q(DB1_URL, "CREATE SCHEMA rightPhant;")
              .then(_ => Calendar.q(DB1_URL,
                                    "CREATE TABLE rightPhant.meetings (" +
                                    "  userid   varchar(10)," +
                                    "  name     text," +
                                    "  address  text," +
                                    "  id       serial" +
                                    ");"))
              .then(_ => Calendar.q(DB1_URL, Lazy
                                    .generate(_ => $insertMeeting.right)
                                    .take(size)
                                    .join("")));

      const leftPromise = Calendar.q(DB2_URL, "CREATE SCHEMA leftPhant;")
              .then(_ => Calendar.q(DB2_URL,
                                    "CREATE TABLE leftPhant.meetings (" +
                                    "  userid   varchar(10)," +
                                    "  date     timestamp with time zone," +
                                    "  id       serial" +
                                    ");"))
              .then(_ => Calendar.q(DB2_URL, Lazy
                                    .generate(_ => $insertMeeting.left)
                                    .take(size)
                                    .join("")));


      return Promise.all([rightPromise, leftPromise]);
    },

    places: function () {
      console.log("phant#places");

      return Calendar
        .q(DB1_URL,
           "SELECT DISTINCT name, address " +
           "FROM rightPhant.meetings " +
           "WHERE userid = 'Alice';");
    },

    meetingsWithBob: function () {
      console.log("phant#meetingsWithBob");

      const encBob = Utils.crypto.encrypt(SKEY, 'Bob');

      var res = {};
      return Calendar
        .q(DB1_URL,
           "SELECT id FROM rightPhant.meetings " +
           "WHERE userid = 'Alice' " +
           "AND address LIKE 'Work' " +
           `AND name LIKE '${JSON.stringify(encBob)}';`)
        .then(ids => {
          const idsStr = Lazy(ids).pluck('id').join(',');
          const query =
                  "SELECT date::date, COUNT(*) FROM leftPhant.meetings " +
                  "WHERE userid = 'Alice' " +
                  "AND (date::date - CURRENT_DATE) BETWEEN 0 and 7 " +
                  `AND id = ANY ('{${idsStr}}'::int[]) ` +
                  "GROUP BY date::date;";

          return JSON.stringify(`${DB2_HTTP}/exec/${query}`);
        });
    },

    meetings: function (limit) {
      console.log("phant#meetings");

      return Calendar
        .q(DB1_URL,
           "SELECT name, address, id " +
           "FROM rightPhant.meetings " +
           "WHERE userid = 'Alice' " +
           `LIMIT ${limit} OFFSET 0;`)
        .then(rows => ({
          right: rows,
          left: `${DB2_HTTP}/exec/` +
            "SELECT date, id " +
            "FROM leftPhant.meetings " +
            "WHERE userid = 'Alice' " +
            `LIMIT ${limit} OFFSET 0;`
        }));
    }
  },

  // --------------------------------------------------------------- utils
  // Executes a query
  q: function(dbUrl, sql) {
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
  },

  dropAll: function() {
    return Calendar.clear.drop()
      .then(_ => Calendar.sym.drop())
      .then(_ => Calendar.frag.drop())
      .then(_ => Calendar.phant.drop());
  },

  // Gets the calendar object based on its namespace
  get: function (namespace) {
    var calendar;

    switch (namespace) {
    case 'sym':
      calendar = Calendar.sym;
      break;
    case 'frag':
      calendar = Calendar.frag;
      break;
    case 'phant':
      calendar = Calendar.phant;
      break;
    default:
      calendar = Calendar.clear;
    }

    return calendar;
  }
};

// Test calendar
Utils.seqPromises([
  // // Clear test
  // _ => Calendar.clear.drop()
  //   .then(_ => Calendar.clear.install(NB_MEETINGS))
  //   .then(_ => Calendar.clear.places())
  //   .then(val => console.log('clear#places: ', val))
  //   .then(_ => Calendar.clear.meetingsWithBob())
  //   .then(val => console.log('clear#meetingsWithBob: ', val))
  //   .then(_ => Calendar.clear.meetings(LIMIT))
  //   .then(val => console.log('clear#meetings: ', val))
  //   .catch(err => console.error(err)),

  // // Sym test
  // _ => Calendar.sym.drop()
  //   .then(_ => Calendar.sym.install(NB_MEETINGS))
  //   .then(_ => Calendar.sym.places())
  //   .then(val => console.log('sym#places: ', val.length))
  //   .then(_ => Calendar.sym.meetingsWithBob())
  //   .then(val => console.log('sym#meetingsWithBob: ', val.length))
  //   .then(_ => Calendar.sym.meetings(LIMIT))
  //   .then(val => console.log('sym#meetings: ', val))
  //   .catch(err => console.error(err)),

  // // Frag test
  // _ => Calendar.frag.drop()
  //   .then(_ => Calendar.frag.install(NB_MEETINGS))
  //   .then(_ => Calendar.frag.places())
  //   .then(val => console.log('frag#places: ', val))
  //   .then(_ => Calendar.frag.meetingsWithBob())
  //   .then(val => console.log('frag#meetingsWithBob: ', val))
  //   .then(_ => Calendar.frag.meetings(LIMIT))
  //   .then(val => console.log('frag#meetings: ', val))
  //   .catch(err => console.error(err)),

  // // Phant test
  // _ => Calendar.phant.drop()
  //   .then(_ => Calendar.phant.install(NB_MEETINGS))
  //   .then(_ => Calendar.phant.places())
  //   .then(val => console.log('phant#places: ', val))
  //   .then(_ => Calendar.phant.meetingsWithBob())
  //   .then(val => console.log('phant#meetingsWithBob: ', val))
  //   .then(_ => Calendar.phant.meetings(LIMIT))
  //   .then(val => console.log('phant#meetings: ', val))
  //   .catch(err => console.error(err)),

  // Drop All
  _ => Calendar.dropAll()
    .then(_ => console.log(true))
    .catch(err => console.error(err)),
]);


// Setup the server
app.set('port', (process.env.PORT || 3000));
app.use(timeout('100s'));

// Basic routing
app.use(express.static(__dirname + '/public'));

// Initializes the database
app.get('/:namespace/install/:size', (req, res) => {
  Calendar
    .get(req.params.namespace)
    .install(+req.params.size)
    .then(val => res.type('json').send(true))
    .catch(err => console.error(err));
});

// Drops the database
app.get('/:namespace/drop', (req, res) => {
  Calendar
    .get(req.params.namespace)
    .drop()
    .then(val => res.type('json').send(true))
    .catch(err => console.error(err));
});

// Alices places visited today
app.get('/:namespace/places', (req, res) => {
  Calendar
    .get(req.params.namespace)
    .places()
    .then(val => res.type('json').send(val))
    .catch(err => console.error(err));
});

// Alice's meetings done last week at work with bob
app.get('/:namespace/meetingsWithBob', (req, res) => {
  Calendar
    .get(req.params.namespace)
    .meetingsWithBob()
    .then(val => res.type('json').send(val))
    .catch(err => console.error(err));
});

// Alice's meetings
app.get('/:namespace/meetings/:limit', (req, res) => {
  Calendar
    .get(req.params.namespace)
    .meetings(+req.params.limit)
    .then(val => res.type('json').send(val))
    .catch(err => console.error(err));
});

// Launch the server
const server = app.listen(app.get('port'), function() {
  const host = server.address().address;
  const port = server.address().port;

  console.log('Example app listening at http://%s:%s', host, port);
});
