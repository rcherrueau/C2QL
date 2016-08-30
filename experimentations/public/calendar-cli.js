const SKEY = 'passwd';
const NB_MEETINGS = 2500;
// const NB_MEETINGS = 500;
// const NB_MEETINGS = 100;
const LIMIT = 2500;
// const LIMIT = 5;

var DEBUG = false;

const Utils = {
  truncateDate: function (date) {
    return new Date(date.getFullYear(), date.getMonth(), date.getDate());
  },

  _sevenDaysMSec: 7 * 24 * 3600 * 1000,

  isNextWeek: function (date) {
    const duration = Utils.truncateDate(date) - Utils.today;

    return duration >= 0 && duration <= Utils._sevenDaysMSec;
  },

  isToday: function (date) {
    const duration = Utils.truncateDate(date) - Utils.today;
    return duration == 0;
  },

  log: function(str, ...args) {
    if (DEBUG) console.log(str, ...args);
  },

  // :: (calendar, [bench]) → Promise bench
  //
  // Generates benchmarks for a specific calendar application. The
  // `benches` argument stores all benches so that you can access them
  // later.
  mkBench: function (cal, benches) {
    // Generates bench for places and meetings
    const bPlaces = new Benchmark(`${cal.name}#places`, function (d) {
      // `this` is the benchmarkjs object. Call `d.resolved()` inside
      // your call back to inform the benchmark lib that the bench
      // ended.
      cal.places(this, d);
    }, { defer: true });

    const bMeetingsWithBob =
            new Benchmark(`${cal.name}#meetingsWithBob`, function (d) {
              cal.meetingsWithBob(this, d);
            }, { defer: true });

    const bMeetings = new Benchmark(`${cal.name}#meetings`, function (d) {
      cal.meetings(this, d);
    }, { defer: true });

    benches.push(bPlaces, bMeetingsWithBob, bMeetings);

    return cal.install()
      .then(_ => Utils.promise.wrapBench(cal, bPlaces))
      .then(_ => Utils.promise.wrapBench(cal, bMeetingsWithBob))
      .then(_ => Utils.promise.wrapBench(cal, bMeetings))
      .then(_ => cal.drop());

  },

  promise: {
    // :: (calendar, bench) → Promise bench
    //
    // Turns a bench execution into a promise.
    wrapBench: function(cal, bench) {
      return new Promise(function (resolve, reject) {
        bench.on('cycle', function(event) {
          console.log(String(event.target));
        }).on('complete', function () {
          // means, times, variance
          console.log(this);
          resolve();
        }).on('abort', function () {
          console.error('abort: ', this);
          reject();
        }).run({async: true});
      });
    },

    // :: [thunk (Promise a)] → Promise [a]
    seq: function (promises) {
      return _.chain(promises)
        .reduce((z, p) => z.then(
          v => p().then(name => {v.push(name); return v;})),
                Promise.resolve([]))
        .value();
    }
  },

  // The crypto part
  crypto: {
    // ;; The algorithm for decryption.
    _algo: { name: 'AES-CBC', length: 256 },

    // :: buffer → (Utils.crypto._algo * iv: buffer)
    //
    // Sets the initialization verctor for the `Utils.crypto._algo`.
    _algoWithIv: function (ivBuffer) {
      const algo = Utils.crypto._algo;
      algo.iv = ivBuffer;

      return algo;
    },

    // :: (buffer, buffer) -> Promise CryptoKey
    //
    // Returns the enhanced key for encryption/decryption.
    //
    // We use pbkdf2 for deriving an enhanced key and prevent from
    // brute force attack by increasing the time it takes to test each
    // possible key.
    //
    // See key stretching.
    // https://en.wikipedia.org/wiki/Key_stretching
    _enhanceKey: function(passphraseBuffer, saltBuffer) {
      return window.crypto.subtle
        // First, wrap the passphrase into a CryptoKey
        .importKey(
          'raw',
          passphraseBuffer,
          {name: 'PBKDF2'},
          true,
          [ 'deriveBits', 'deriveKey' ])
        // Then derive the key
        .then(passphraseCrypto => window.crypto.subtle.deriveKey(
          { // The algorithm for key enhancement. Use the same
            // algorithm than the one uses in calendar-saas.
            name: 'PBKDF2',
            salt: saltBuffer,
            iterations: 100,
            hash: 'SHA-256'
          },
          passphraseCrypto, // The passphrase wrap into a `CryptoKey`
          Utils.crypto._algo, // key for what kind of encryption
          true, // The key can be inspected?
          [ 'encrypt', 'decrypt' ] // key usage
        ));
    },

    // :: (string, {value: hex string, salt: string, iv: hex string}) →
    //      Promise Uint8Array
    //
    // Decrypts a cipher object with the given passphrase.
    decrypt : function (passphrase, cipher) {
      // Loads passphrase, cipherText, salt, iv into a buffer.
      const passphraseBuffer = Unibabel.utf8ToBuffer(passphrase);
      const cipherTextBuffer = Unibabel.hexToBuffer(cipher.value);
      const saltBuffer = Unibabel.utf8ToBuffer(cipher.salt);
      const ivBuffer = Unibabel.hexToBuffer(cipher.iv);

      return Utils.crypto
        ._enhanceKey(passphraseBuffer, saltBuffer)
        .then(cryptoKey => window.crypto.subtle.decrypt(
          Utils.crypto._algoWithIv(ivBuffer),
          cryptoKey,
          cipherTextBuffer
        ))
        .then(res => new Uint8Array(res));
    },

    // :: (string, {value: hex string, salt: string, iv: hex string}) →
    //      Promise meeting
    //
    // Decrypts a ciphered meeting with the given passphrase.
    decryptMeeting(passphrase, cipherMeeting) {
      return Utils.crypto
        .decrypt(passphrase, cipherMeeting)
        .then(clearBuffer => Unibabel.bufferToUtf8(clearBuffer))
        .then(m => JSON.parse(m))
        .then(m => {m.date = new Date(m.date); return m;});
    }
  },

  fixpoint: function () {
    this.today = this.truncateDate(new Date());
    this.heightDays = new Date(this.today.getFullYear(),
                               this.today.getMonth(),
                               this.today.getDate() + 8);
    return this;
  }
}.fixpoint();

const Calendar = {
  // ---------------------------------------------------- namespace: clear
  clear: {
    drop: function () {
      return fetch('/clear/drop');
    },

    // Install the database
    install: function () {
      return fetch(`/clear/install/${NB_MEETINGS}`);
    },

    places: function (benchjs, deferred) {
      fetch('/clear/places')
        .then(response => response.json())
        .then(res => {
          Utils.log("clear#places: ", res);
          if (_.hasIn(deferred, 'resolve')) {
            deferred.resolve();
          }
        })
        .catch(err => {
          benchjs.abort();
          console.error(err);
        });
    },

    meetingsWithBob: function (benchjs, deferred) {
      fetch('/clear/meetingsWithBob')
        .then(response => response.json())
        .then(res => {
          Utils.log("clear#meetingsWithBob: ", res);
          if (_.hasIn(deferred, 'resolve')) {
            deferred.resolve();
          }
        })
        .catch(err => {
          benchjs.abort();
          console.error(err);
        });
    },

    meetings: function (benchjs, deferred) {
      fetch(`/clear/meetings/${LIMIT}`)
        .then(response => response.json())
        .then(rows => {
          // Get the date object back
          const res = _.chain(rows)
                  .map(m => { m.date = new Date(m.date); return m; })
                  .value();
          Utils.log("clear#meetings: ", res);
          if (_.hasIn(deferred, 'resolve')) {
            deferred.resolve();
          }
        })
        .catch(err => {
          benchjs.abort();
          console.error(err);
        });
    },

    name: "Calendar.clear"
  },

  // ----------------------------------------------------- namespace: sym
  sym: {
    drop: function () {
      return fetch('/sym/drop');
    },

    install: function () {
      return fetch(`/sym/install/${NB_MEETINGS}`);
    },

    places: function (benchjs, deferred) {
      fetch('/sym/places')
        .then(response => response.json())
        .then(meetings => {
          Promise
            .all(_.chain(meetings)
                 .map(({meeting}) => JSON.parse(meeting))
                 .map(cipher => Utils.crypto.decryptMeeting(SKEY, cipher))
                 .toArray())
            .then(meetings => _.chain(meetings)
                  .map(({name, address}) => ({name: name, address: address}))
                  .uniqBy(({name, address}) => name+address)
                  .filter(({name}) => name.startsWith('B'))
                  .value())
            .then(res => {
              Utils.log("sym#places: ", res);
              if (_.hasIn(deferred, 'resolve')) {
                deferred.resolve();
              }
            })
            .catch(err => {
              console.error(err);
              benchjs.abort();
            });
        })
        .catch(err => {
          console.error(err);
          benchjs.abort();
        });
    },

    meetingsWithBob: function (benchjs, deferred) {
      fetch('/sym/meetingsWithBob')
        .then(response => response.json())
        .then(meetings => {
          Promise
            .all(_.chain(meetings)
                 .map(({meeting}) => JSON.parse(meeting))
                 .map(cipher => Utils.crypto.decryptMeeting(SKEY, cipher))
                 .toArray())
            .then(meetings => _.chain(meetings)
                  .filter(({date}) => Utils.isNextWeek(date))
                  .filter(({address}) => address === 'Work')
                  .filter(({name}) => name === 'Bob')
                  .countBy(({date}) => Utils.truncateDate(date))
                  .value())
            .then(res => {
              Utils.log("sym#meetingsWithBob: ", res);
              if (_.hasIn(deferred, 'resolve')) {
                deferred.resolve();
              }
            })
            .catch(err => {
              console.error(err);
              benchjs.abort();
            });
        })
        .catch(err => {
          console.error(err);
          benchjs.abort();
        });
    },

    meetings: function (benchjs, deferred) {
      fetch(`/sym/meetings/${LIMIT}`)
        .then(response => response.json())
        .then(meetings => {
          Promise
            .all(_.chain(meetings)
                 .map(({meeting}) => JSON.parse(meeting))
                 .map(cipher => Utils.crypto.decryptMeeting(SKEY, cipher))
                 .toArray())
            .then(res => {
              Utils.log("sym#meetings: ", res);
              if (_.hasIn(deferred, 'resolve')) {
                deferred.resolve();
              }
            })
            .catch(err => {
              console.error(err);
              benchjs.abort();
            });
        })
        .catch(err => {
          console.error(err);
          benchjs.abort();
        });
    },

    name: "Calendar.sym"
  },

  // ----------------------------------------------------- namespace: frag
  frag: {
    drop: function () {
      return fetch('frag/drop');
    },

    // Install the database
    install: function () {
      return fetch(`/frag/install/${NB_MEETINGS}`);
    },

    places: function (benchjs, deferred) {
      fetch('/frag/places')
        .then(response => response.json())
        .then(res => {
          Utils.log("frag#places: ", res);
          if (_.hasIn(deferred, 'resolve')) {
            deferred.resolve();
          }
        })
        .catch(err => {
          benchjs.abort();
          console.error(err);
        });
    },

    meetingsWithBob: function (benchjs, deferred) {
      fetch('/frag/meetingsWithBob')
        .then(response => response.json())
        .then(res => {
          Utils.log("frag#meetingsWithBob: ", res);
          if (_.hasIn(deferred, 'resolve')) {
            deferred.resolve();
          }
        })
        .catch(err => {
          benchjs.abort();
          console.error(err);
        });
    },

    meetings: function (benchjs, deferred) {
      fetch(`/frag/meetings/${LIMIT}`)
        .then(response => response.json())
        .then(rows => {
          const res = _.chain(rows)
                  .map(m => { m.date = new Date(m.date); return m; })
                  .value();
          Utils.log("frag#meetings: ", res);
          if (_.hasIn(deferred, 'resolve')) {
            deferred.resolve();
          }
        })
        .catch(err => {
          benchjs.abort();
          console.error(err);
        });
    },

    name: "Calendar.frag"
  },

  // --------------------------------------------------- namespace: client
  client: {
    drop: function () {
      Calendar.client._db = new Array(NB_MEETINGS);
      return Promise.resolve();
    },

    install: function () {
      // The meeting to add
      const meeting = {
        date: new Date(),
        name: "Bob",
        address: "Work"
      };

      _.fill(Calendar.client._db, meeting);

      return Promise.resolve();
    },

    places: function (benchjs, deferred) {
      const res = _.chain(Calendar.client._db)
              .map(({name, address}) => ({name: name, address: address}))
              .uniqBy(({name, address}) => name+address)
              .filter(({name}) => name.startsWith('B'))
              .value();

      Utils.log("client#places: ", res);
      if (_.hasIn(deferred, 'resolve')) {
        deferred.resolve();
      }
    },

    meetingsWithBob: function (benchjs, deferred) {
      const res = _.chain(Calendar.client._db)
              .filter(({date}) => Utils.isNextWeek(date))
              .filter(({address}) => address === 'Work')
              .filter(({name}) => name === 'Bob')
              .countBy(({date}) => Utils.truncateDate(date))
              .value();

      Utils.log("client#meetingsWithBob: ", res);
      if (_.hasIn(deferred, 'resolve')) {
        deferred.resolve();
      }
    },

    meetings: function (benchjs, deferred) {
      const res = _.chain(Calendar.client._db)
              .take(LIMIT)
              .value();

      Utils.log("client#meetings: ", res);
      if (_.hasIn(deferred, 'resolve')) {
        deferred.resolve();
      }
    },

    name: "Calendar.client",

    _db: new Array(NB_MEETINGS)

  },

  // ---------------------------------------------------- namespace: phant
  phant : {
    drop: function () {
      return fetch('/phant/drop');
    },

    // Install the database
    install: function () {
      return fetch(`/phant/install/${NB_MEETINGS}`);
    },

    places: function (benchjs, deferred) {
      fetch('/phant/places')
        .then(response => response.json())
        .then(rows => {
          Utils.promise
            .seq(_.chain(rows)
                 .map(m => (_ =>
                            Calendar.phant
                            ._decryptNameWithMemoization(
                              JSON.parse(m.name))
                            .then(name => ({
                              name: name,
                              address: m.address
                            }))))
                 .value())
            .then(res => Promise.resolve(_.filter(res, ({name}) =>
                                                  name.startsWith('B'))))
            .then(res => {
              Utils.log("phant#places: ", res);
              if (_.hasIn(deferred, 'resolve')) {
                deferred.resolve();
              }
            })
            .catch(err => {
              console.error(err);
              benchjs.abort();
            });
        });
    },

    meetingsWithBob: function (benchjs, deferred) {
      fetch('/phant/meetingsWithBob')
        .then(response => response.json())
        .then(k => fetch(k).then(resp => resp.json()))
        .then(rows => rows.map(r => {
          var obj = {};
          obj[new Date(r.date)] = +r.count;
          return obj;
        }))
        .then(res => {
          Utils.log("phant#meetingsWithBob: ", res[0]);
          if (_.hasIn(deferred, 'resolve')) {
            deferred.resolve();
          }
        })
        .catch(err => {
          benchjs.abort();
          console.error(err);
        });
    },

    meetings: function (benchjs, deferred) {
      fetch(`/phant/meetings/${LIMIT}`)
        .then(response => response.json())
        .then(({left, right}) =>
              Promise.all([fetch(left).then(resp => resp.json()), right]))
        // Manage left and right
        .then(([lRows, rRows]) => {

          const rows = _.zipWith(
            _.sortBy(lRows, 'id'),
            _.sortBy(rRows, 'id'),
            (lr, rr) => ({
              date: new Date(lr.date),
              name: JSON.parse(rr.name),
              address: rr.address
            }));

          Utils.promise
            .seq(_.chain(rows)
                 .map(
                   m => (
                     _ => Calendar.phant
                       ._decryptNameWithMemoization(m.name)
                       .then(name => ({
                         date: m.date,
                         name: name,
                         address: m.address
                       }))))
                 .value())
            .then(res => {
              Utils.log("phant#meetings: ", res);
              if (_.hasIn(deferred, 'resolve')) {
                deferred.resolve();
              }
            })
            .catch(err => {
              console.error(err);
              benchjs.abort();
            });
        })
        .catch(err => {
          console.error(err);
          benchjs.abort();
        });
    },

    _memoizeName: new Map(),

    _decryptNameWithMemoization: function (cipherName) {
      var namePromise;
      const memoKey = cipherName.value + cipherName.salt + cipherName.iv;

      if (Calendar.phant._memoizeName.has(memoKey)) {
        namePromise =
          Promise.resolve(Calendar.phant._memoizeName.get(memoKey));
      } else {
        namePromise =
          Utils.crypto.decrypt(SKEY, cipherName)
          .then(clearBuffer => {
            const name = Unibabel.bufferToUtf8(clearBuffer);
            Calendar.phant._memoizeName.set(memoKey, name);
            return name;
          });
      }

      return namePromise;
    },

    name: "Calendar.phant"
  },

  // --------------------------------------------------------------- utils
  dropAll : function() {
    return Calendar.clear.drop()
      .then(_ => Calendar.sym.drop())
      .then(_ => Calendar.frag.drop())
      .then(_ => Calendar.phant.drop());
  },


  testAll : function () {
    DEBUG = true;

    Utils.promise.seq([
      _ => Calendar.client.drop()
        .then(_ => Calendar.client.install())
        .then(_ => Calendar.client.places())
        .then(_ => Calendar.client.meetingsWithBob())
        .then(_ => Calendar.client.meetings()),

      _ => Calendar.clear.drop()
        .then(_ => Calendar.clear.install())
        .then(_ => Calendar.clear.places())
        .then(_ => Calendar.clear.meetingsWithBob())
        .then(_ => Calendar.clear.meetings()),

      _ => Calendar.sym.drop()
        .then(_ => Calendar.sym.install())
        .then(_ => Calendar.sym.places())
        .then(_ => Calendar.sym.meetingsWithBob())
        .then(_ => Calendar.sym.meetings()),

      _ => Calendar.frag.drop()
        .then(_ => Calendar.frag.install())
        .then(_ => Calendar.frag.places())
        .then(_ => Calendar.frag.meetingsWithBob())
        .then(_ => Calendar.frag.meetings()),

      _ => Calendar.phant.drop()
        .then(_ => Calendar.phant.install())
        .then(_ => Calendar.phant.places())
        .then(_ => Calendar.phant.meetingsWithBob())
        .then(_ => Calendar.phant.meetings()),

      _ => Calendar.dropAll(),
    ])
    .then(_ => DEBUG = false)
    .catch(err => console.error(err));
  },

  // ;; Gets the sql object based on its namespace
  get : function (namespace) {
    var cal;

    switch (namespace) {
    case 'sym':
      cal = Calendar.sym;
      break;
    case 'frag':
      cal = Calendar.frag;
      break;
    case 'client':
      cal = Calendar.client;
      break;
    case 'phant':
      cal = Calendar.phant;
      break;
    default:
      cal = Calendar.clear;
    }

    return cal;
  }
};

document.addEventListener('DOMContentLoaded', () => {
  // ;; The start button
  const $start = document.getElementById('benches-start');

  $start.addEventListener('click', () => {
    // ;; Container for all bench
    const benches = [];

    // ;; div to display result
    const $res = document.getElementById('benches-res');

    // The benchmark
    Utils.mkBench(Calendar.get('client'), benches)
      .then(_ => Utils.mkBench(Calendar.get('clear'), benches))
      .then(_ => Utils.mkBench(Calendar.get('sym'), benches))
      .then(_ => Utils.mkBench(Calendar.get('frag'), benches))
      .then(_ => Utils.mkBench(Calendar.get('phant'), benches))
      .then(() => {
        const nameRE = /Calendar\.(.+?)#.+/;
        const placesRE = /Calendar\.(.+?)#places/;
        const meetingsWithBobRE = /Calendar\.(.+?)#meetingsWithBob/;
        const meetingsRE = /Calendar\.(.+?)#meetings$/;

        const type = "# " + _.chain(benches)
                .map(({name}) => name.match(nameRE))
                .map(([_, name]) => name)
                .uniq()
                .join(' ');

        // Places
        const places = "Places " + _.chain(benches)
                .filter(({name}) => placesRE.test(name))
                .map(({stats}) => stats.mean)
                .join(' ');

        // Meetings with Bob
        const meetingsWithBob = "MeetingsW/Bob " + _.chain(benches)
                .filter(({name}) => meetingsWithBobRE.test(name))
                .map(({stats}) => stats.mean)
                .join(' ');

        // All meetings
        const meetings = "AllMeetings " + _.chain(benches)
                .filter(({name}) => meetingsRE.test(name))
                .map(({stats}) => stats.mean)
                .join(' ');

        $res.insertAdjacentHTML(
          'beforeend',
          type + '\n' + places + '\n' + meetingsWithBob + '\n' + meetings);
      });
  }, false);
}, false);
