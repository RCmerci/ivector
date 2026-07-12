(ns rrbvec.benchmark-js)

(def default-size 20000)
(def default-reads 10000)
(def default-updates 5000)
(def default-iterations 20)
(def concat-chunks 100)
(defonce benchmark-sink (volatile! nil))

(defn parse-int-arg [value flag]
  (let [parsed (js/Number value)]
    (when (or (js/Number.isNaN parsed) (not (integer? parsed)) (neg? parsed))
      (throw (js/Error. (str flag " must be a non-negative integer"))))
    parsed))

(defn parse-config [argv]
  (loop [args (seq argv)
         config {:size default-size
                 :reads default-reads
                 :updates default-updates
                 :iterations default-iterations}]
    (if (nil? args)
      config
      (let [flag (first args)
            value (second args)]
        (case flag
          "--size" (recur (nnext args) (assoc config :size (parse-int-arg value flag)))
          "--reads" (recur (nnext args) (assoc config :reads (parse-int-arg value flag)))
          "--updates" (recur (nnext args) (assoc config :updates (parse-int-arg value flag)))
          "--iterations" (recur (nnext args) (assoc config :iterations (parse-int-arg value flag)))
          (throw (js/Error. (str "unexpected argument: " flag))))))))

(defn make-indices [count modulo-by]
  (mapv (fn [i] (mod (+ (* i 1103) 12345) modulo-by)) (range count)))

(defn range-sum [start length]
  (/ (* (+ start start length -1) length) 2))

(defn cljs-build-back [size]
  (loop [i 0
         values []]
    (if (= i size)
      values
      (recur (inc i) (conj values i)))))

(defn cljs-build-front [size]
  (loop [i 0
         values []]
    (if (= i size)
      values
      (recur (inc i) (into [i] values)))))

(defn cljs-random-read [values indices]
  (reduce (fn [acc index] (+ acc (nth values index))) 0 indices))

(defn cljs-random-write [values indices]
  (reduce-kv
    (fn [values update-index value-index]
      (assoc values value-index (- (inc update-index))))
    values
    indices))

(defn cljs-sum [values]
  (reduce + 0 values))

(defn cljs-fold-ignore [values]
  (reduce (fn [_ value] value) 0 values))

(defn cljs-map-values [values]
  (mapv (fn [value] (+ (* value 2) 1)) values))

(defn cljs-repeated-subvec [values steps]
  (loop [steps steps
         values values]
    (if (zero? steps)
      values
      (recur (dec steps) (subvec values 1 (dec (count values)))))))

(defn chunk-bounds [size chunks]
  (let [base (quot size chunks)
        remainder (mod size chunks)]
    (mapv
      (fn [index]
        (let [length (+ base (if (< index remainder) 1 0))
              start (+ (* index base) (min index remainder))]
          [start length]))
      (range chunks))))

(defn cljs-concat-chunks [values chunks]
  (reduce
    (fn [acc [start length]]
      (into acc (subvec values start (+ start length))))
    []
    (chunk-bounds (count values) chunks)))

(defn cljs-build-chunks [values chunks]
  (mapv
    (fn [[start length]]
      (subvec values start (+ start length)))
    (chunk-bounds (count values) chunks)))

(defn cljs-concat-built-chunks [chunks]
  (vec (apply concat chunks)))

(defn cljs-pop-back-all [values]
  (loop [values values]
    (if (empty? values)
      values
      (recur (pop values)))))

(defn cljs-pop-front-all [values]
  (loop [values values]
    (if (empty? values)
      values
      (recur (subvec values 1)))))

(defn cljs-push-pop [size]
  (cljs-pop-back-all (cljs-build-back size)))

(defn cljs-concat-map-singleton [values]
  (into [] (mapcat (fn [value] [value])) values))

(defn cljs-concat-map-pair [values]
  (into [] (mapcat (fn [value] [value (- value)])) values))

(defn cljs-concat-map-mostly-empty [values]
  (into []
        (mapcat (fn [value]
                  (if (zero? (mod value 10)) [value] [])))
        values))

(defn cljs-concat-map-constant [values mapped]
  (into [] (mapcat (constantly mapped)) values))

(defn js-backend [name api]
  {:name name
   :build-back #(.buildBack api %)
   :build-front #(.buildFront api %)
   :length #(.length api %)
   :sum #(.sum api %)
   :fold-ignore #(.foldIgnore api %)
   :random-read #(.randomRead api %1 %2)
   :random-write #(.randomWrite api %1 %2)
   :map-values #(.mapValues api %)
   :repeated-subvec #(.repeatedSubvec api %1 %2)
   :build-chunks #(.buildChunks api %1 %2)
   :concat-built-chunks #(.concatBuiltChunks api %)
   :concat-chunks #(.concatChunks api %1 %2)
   :pop-back-all #(.popBackAll api %)
   :pop-front-all #(.popFrontAll api %)
   :push-pop #(.pushPop api %)
   :concat-map-singleton #(.concatMapSingleton api %)
   :concat-map-pair #(.concatMapPair api %)
   :concat-map-mostly-empty #(.concatMapMostlyEmpty api %)
   :concat-map-constant #(.concatMapConstant api %1 %2)})

(defn cljs-backend [indices]
  {:name "cljs vector"
   :build-back cljs-build-back
   :build-front cljs-build-front
   :length count
   :sum cljs-sum
   :fold-ignore cljs-fold-ignore
   :random-read (fn [values _count] (cljs-random-read values (:reads indices)))
   :random-write (fn [values _count] (cljs-random-write values (:updates indices)))
   :map-values cljs-map-values
   :repeated-subvec cljs-repeated-subvec
   :build-chunks cljs-build-chunks
   :concat-built-chunks cljs-concat-built-chunks
   :concat-chunks cljs-concat-chunks
   :pop-back-all cljs-pop-back-all
   :pop-front-all cljs-pop-front-all
   :push-pop cljs-push-pop
   :concat-map-singleton cljs-concat-map-singleton
   :concat-map-pair cljs-concat-map-pair
   :concat-map-mostly-empty cljs-concat-map-mostly-empty
   :concat-map-constant cljs-concat-map-constant})

(defn check [label expected actual]
  (when-not (= expected actual)
    (throw (js/Error. (str label ": expected " expected ", got " actual)))))

(defn verify-backend [backend config expected-sum]
  (let [size (:size config)
        reads (:reads config)
        updates (:updates config)
        subvec-steps (min 8 (quot (dec size) 2))
        values ((:build-back backend) size)
        front-values ((:build-front backend) size)
        updated ((:random-write backend) values updates)
        mapped ((:map-values backend) values)
        sliced ((:repeated-subvec backend) values subvec-steps)
        chunks ((:build-chunks backend) values (min concat-chunks size))
        concatenated ((:concat-built-chunks backend) chunks)
        concat-map-input ((:build-back backend) 20)
        concat-map-singletons ((:concat-map-singleton backend) concat-map-input)
        concat-map-pairs ((:concat-map-pair backend) concat-map-input)
        concat-map-mostly-empty ((:concat-map-mostly-empty backend) concat-map-input)
        concat-map-constant
        ((:concat-map-constant backend)
         ((:build-back backend) 3)
         ((:build-back backend) 33))]
    (check (str (:name backend) " build length") size ((:length backend) values))
    (check (str (:name backend) " build sum") expected-sum ((:sum backend) values))
    (check (str (:name backend) " front length") size ((:length backend) front-values))
    (check (str (:name backend) " front sum") expected-sum ((:sum backend) front-values))
    (check (str (:name backend) " read sum") ((:random-read backend) values reads) ((:random-read backend) values reads))
    (check (str (:name backend) " update length") size ((:length backend) updated))
    (check (str (:name backend) " map length") size ((:length backend) mapped))
    (check (str (:name backend) " map sum") (+ (* 2 expected-sum) size) ((:sum backend) mapped))
    (check (str (:name backend) " subvec length") (- size (* 2 subvec-steps)) ((:length backend) sliced))
    (check (str (:name backend) " concat length") size ((:length backend) concatenated))
    (check (str (:name backend) " concat_map singleton length") 20 ((:length backend) concat-map-singletons))
    (check (str (:name backend) " concat_map pair length") 40 ((:length backend) concat-map-pairs))
    (check (str (:name backend) " concat_map mostly-empty length") 2 ((:length backend) concat-map-mostly-empty))
    (check (str (:name backend) " concat_map constant length") 99 ((:length backend) concat-map-constant))
    (check (str (:name backend) " pop_back length") 0 ((:length backend) ((:pop-back-all backend) values)))
    (check (str (:name backend) " pop_front length") 0 ((:length backend) ((:pop-front-all backend) values)))
    (check (str (:name backend) " push_pop length") 0 ((:length backend) ((:push-pop backend) size)))))

(defn benchmark [iterations f]
  (let [start (.now js/performance)]
    (dotimes [_ iterations]
      (vreset! benchmark-sink (f)))
    (/ (- (.now js/performance) start) iterations)))

(defn cases [backend config values]
  (let [size (:size config)
        reads (:reads config)
        updates (:updates config)
        subvec-steps (min 8 (quot (dec size) 2))
        build-back (:build-back backend)
        build-front (:build-front backend)
        fold-ignore (:fold-ignore backend)
        map-values (:map-values backend)
        random-read (:random-read backend)
        random-write (:random-write backend)
        repeated-subvec (:repeated-subvec backend)
        build-chunks (:build-chunks backend)
        concat-built-chunks (:concat-built-chunks backend)
        pop-back-all (:pop-back-all backend)
        pop-front-all (:pop-front-all backend)
        push-pop (:push-pop backend)
        concat-map-singleton (:concat-map-singleton backend)
        concat-map-pair (:concat-map-pair backend)
        concat-map-mostly-empty (:concat-map-mostly-empty backend)
        concat-map-constant (:concat-map-constant backend)
        concat-map-singleton-input (build-back 20000)
        concat-map-pair-input (build-back 10000)
        concat-map-mostly-empty-input (build-back 20000)
        concat-map-chunk-input (build-back 5000)
        concat-map-1024-input (build-back 200)
        concat-map-one-large-input (build-back 1)
        concat-map-two-large-input (build-back 2)
        concat-map-33-values (build-back 33)
        concat-map-1024-values (build-back 1024)
        concat-map-large-values (build-back 1000000)
        chunks (build-chunks values (min concat-chunks size))]
    [{:group "Sequential write" :name "push_back" :run #(build-back size)}
     {:group "Sequential write" :name "push_front" :run #(build-front size)}
     {:group "Sequential read" :name "fold/ignore" :run #(fold-ignore values)}
     {:group "Sequential read" :name "map" :run #(map-values values)}
     {:group "Random read" :name "indexed reads" :run #(random-read values reads)}
     {:group "Random write" :name "indexed writes" :run #(random-write values updates)}
     {:group "Subvec and concat" :name "repeated subvec" :run #(repeated-subvec values subvec-steps)}
     {:group "Subvec and concat" :name "concat chunks" :run #(concat-built-chunks chunks)}
     {:group "Push/pop" :name "pop_back all" :run #(pop-back-all values)}
     {:group "Push/pop" :name "pop_front all" :run #(pop-front-all values)}
     {:group "Push/pop" :name "push then pop" :run #(push-pop size)}
     {:group "Concat map" :name "20k singleton" :run #(concat-map-singleton concat-map-singleton-input)}
     {:group "Concat map" :name "10k pair" :run #(concat-map-pair concat-map-pair-input)}
     {:group "Concat map" :name "20k mostly empty" :run #(concat-map-mostly-empty concat-map-mostly-empty-input)}
     {:group "Concat map" :name "5k x 33 elements" :run #(concat-map-constant concat-map-chunk-input concat-map-33-values)}
     {:group "Concat map" :name "200 x 1024 elements" :run #(concat-map-constant concat-map-1024-input concat-map-1024-values)}
     {:group "Concat map" :name "one large vector" :run #(concat-map-constant concat-map-one-large-input concat-map-large-values)}
     {:group "Concat map" :name "two large vectors" :run #(concat-map-constant concat-map-two-large-input concat-map-large-values)}]))

(defn print-results [results]
  (doseq [[group rows] (group-by :group results)]
    (println (str "*" group "*"))
    (doseq [row (sort-by :ms rows)]
      (println
        (str "  "
             (.padEnd (str (:backend row) " " (:name row)) 42)
             (.toFixed (:ms row) 6)
             " ms/run")))
    (println)))

(defn -main [& main-argv]
  (let [node-require (js* "require")
        argv (if (seq main-argv) main-argv (.slice js/process.argv 2))
        config (parse-config argv)]
    (when (<= (:size config) 0)
      (throw (js/Error. "--size must be positive")))
    (set! js/process.env.NODE_PATH
          (or js/process.env.RRBVEC_MELANGE_NODE_PATH
              js/process.env.NODE_PATH
              "benchmark-melange/node_modules"))
    (. (node-require "module") _initPaths)
    (node-require (or js/process.env.RRBVEC_JSOO_JS "./benchmark_jsoo.bc.js"))
    (node-require
      (or js/process.env.RRBVEC_MELANGE_JS
          "./benchmark-melange/bin/benchmark_melange.js"))
    (let [indices {:reads (make-indices (:reads config) (:size config))
                   :updates (make-indices (:updates config) (:size config))}
          expected-sum (range-sum 0 (:size config))
          backends [(cljs-backend indices)
                    (js-backend "jsoo rrbvec" js/globalThis.rrbvecJsoo)
                    (js-backend "melange rrbvec" js/globalThis.rrbvecMelange)]]
      (println "Benchmark engine: ClojureScript/node performance.now")
      (println
        (str "size=" (:size config)
             " reads=" (:reads config)
             " updates=" (:updates config)
             " iterations=" (:iterations config)))
      (println)
      (doseq [backend backends]
        (verify-backend backend config expected-sum))
      (->> backends
           (mapcat
             (fn [backend]
               (let [values ((:build-back backend) (:size config))]
                 (map
                   (fn [case]
                     {:group (:group case)
                      :backend (:name backend)
                      :name (:name case)
                      :ms (benchmark (:iterations config) (:run case))})
                   (cases backend config values)))))
           print-results))))

(set! *main-cli-fn* -main)
