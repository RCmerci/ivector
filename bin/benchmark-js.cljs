(ns rrbvec.benchmark-js)

(def default-size 20000)
(def default-reads 10000)
(def default-updates 5000)
(def default-iterations 20)
(def concat-chunks 100)

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

(defn js-backend [name api]
  {:name name
   :build-back #(.buildBack api %)
   :build-front #(.buildFront api %)
   :length #(.length api %)
   :sum #(.sum api %)
   :random-read #(.randomRead api %1 %2)
   :random-write #(.randomWrite api %1 %2)
   :map-values #(.mapValues api %)
   :repeated-subvec #(.repeatedSubvec api %1 %2)
   :build-chunks #(.buildChunks api %1 %2)
   :concat-built-chunks #(.concatBuiltChunks api %)
   :concat-chunks #(.concatChunks api %1 %2)
   :pop-back-all #(.popBackAll api %)
   :pop-front-all #(.popFrontAll api %)
   :push-pop #(.pushPop api %)})

(defn cljs-backend [indices]
  {:name "cljs vector"
   :build-back cljs-build-back
   :build-front cljs-build-front
   :length count
   :sum cljs-sum
   :random-read (fn [values _count] (cljs-random-read values (:reads indices)))
   :random-write (fn [values _count] (cljs-random-write values (:updates indices)))
   :map-values cljs-map-values
   :repeated-subvec cljs-repeated-subvec
   :build-chunks cljs-build-chunks
   :concat-built-chunks cljs-concat-built-chunks
   :concat-chunks cljs-concat-chunks
   :pop-back-all cljs-pop-back-all
   :pop-front-all cljs-pop-front-all
   :push-pop cljs-push-pop})

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
        concatenated ((:concat-built-chunks backend) chunks)]
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
    (check (str (:name backend) " pop_back length") 0 ((:length backend) ((:pop-back-all backend) values)))
    (check (str (:name backend) " pop_front length") 0 ((:length backend) ((:pop-front-all backend) values)))
    (check (str (:name backend) " push_pop length") 0 ((:length backend) ((:push-pop backend) size)))))

(defn benchmark [iterations f]
  (let [start (.now js/performance)]
    (dotimes [_ iterations]
      (f))
    (/ (- (.now js/performance) start) iterations)))

(defn cases [backend config values]
  (let [size (:size config)
        reads (:reads config)
        updates (:updates config)
        subvec-steps (min 8 (quot (dec size) 2))
        chunks ((:build-chunks backend) values (min concat-chunks size))]
    [{:group "Sequential write" :name "push_back" :run #((:build-back backend) size)}
     {:group "Sequential write" :name "push_front" :run #((:build-front backend) size)}
     {:group "Sequential read" :name "fold/sum" :run #((:sum backend) values)}
     {:group "Sequential read" :name "map" :run #((:map-values backend) values)}
     {:group "Random read" :name "indexed reads" :run #((:random-read backend) values reads)}
     {:group "Random write" :name "indexed writes" :run #((:random-write backend) values updates)}
     {:group "Subvec and concat" :name "repeated subvec" :run #((:repeated-subvec backend) values subvec-steps)}
     {:group "Subvec and concat" :name "concat chunks" :run #((:concat-built-chunks backend) chunks)}
     {:group "Push/pop" :name "pop_back all" :run #((:pop-back-all backend) values)}
     {:group "Push/pop" :name "pop_front all" :run #((:pop-front-all backend) values)}
     {:group "Push/pop" :name "push then pop" :run #((:push-pop backend) size)}]))

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
