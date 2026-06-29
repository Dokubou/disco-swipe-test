/* ============================================================
   Disco Swipe — 縦スワイプ式 音楽ディスカバリー (Vanilla JS)
   - iTunesプール(musics.json)を読み、ジャンル問わずランダム再生
   - 右:キープ / 左:スキップ / 上:Apple Musicプレイリスト追加
   - スワイプ連打に耐える軽量設計 + iOS Safari の描画残像/ズーム対策
   ============================================================ */
(function () {
  "use strict";

  /* ---------- 設定値 ---------- */
  var SWIPE_DIST = 70;     // スワイプ確定の移動量(px)
  var SWIPE_VEL = 0.5;     // スワイプ確定の速度(px/ms)
  var SWIPE_MIN_MOVE = 8;  // この距離動いたら即「スワイプ」確定(手回しに化けさせない)
  var SCRUB_HOLD_MS = 220; // ほぼ静止でこの時間長押しすると「手回し(スクラッチ)」モード
  var SEC_PER_DEG = 8 / 360; // 1回転(360°)で約8秒ぶん曲を進める/戻す
  var TAP_DIST = 10, TAP_MS = 300; // タップ(再生/停止)判定
  var OUT_MS = 240;        // フリング(画面外へ)アニメ時間
  var SPEED_DIST = 60;     // 下にこの距離下げると2倍速モード
  var SPEED_RATE = 2;      // 2倍速
  var IN_MS = 240;         // 新カードが入ってくるアニメ時間
  var RING_LEN = 301.59;   // プログレスリング円周(2πr, r=48)
  var ROT_DEG_PER_MS = 360 / 4200; // 自動回転の速さ(1回転4.2秒)
  var LS_FAV = "discoSwipe.fav.v1";
  var LS_APPLE = "discoSwipe.apple.v1";
  var LS_SEEN = "discoSwipe.seen.v1";
  var LS_LISTEN = "discoSwipe.listen.v1";  // アーティスト/ジャンル別の累計再生秒数(おすすめ学習用)
  var SEEN_CAP = 12000;    // 直近この数の再生済み曲を覚えておき、次回以降は後回しにする(毎回違う流れにする)
  // お気に入り: 総当たりの中でこの倍率ぶん多めに(分散させて)出すアーティスト
  var ARTIST_BOOST = { "BTS": 3, "SEVENTEEN": 3 };
  // コラボが主流のジャンル: ソロ優先(soloBias/soloFirst)を解除してコラボ曲も普通に流す
  var COLLAB_OK = { "hiphop_jp": 1 };

  /* ---------- 状態 ---------- */
  var state = {
    tracks: [],     // 読み込んだ楽曲プール
    order: [],      // シャッフル済みの再生列(履歴も兼ねる)
    pos: 0,         // order内の現在位置
    bucket: "osusume", // 選択中のジャンル(osusume=おすすめ / all=全ジャンル均等ランダム)
    started: false, // ユーザー操作でオーディオ解放済みか
    playing: false,
    autoSkip: localStorage.getItem("discoSwipe.autoSkip") === "1", // 曲が終わると自動で次へ
    scrubbing: false, // レコード手回し(スクラッチ)中か
    locked: false,  // 遷移アニメ中のロック(連打の整合性確保)
    fav: loadLS(LS_FAV),
    apple: loadLS(LS_APPLE),
    seen: loadLS(LS_SEEN),                                       // 最近再生した曲のID(後回し用)
    listen: loadListen(),                                        // {a:{アーティスト:秒}, b:{ジャンル:秒}} 累計再生時間
    appleConnected: false,                                       // Apple Music連携済みか
    applePlaylistId: localStorage.getItem("discoSwipe.applePlaylistId") || ""
  };
  state.seenSet = {};
  state.seen.forEach(function (id) { state.seenSet[id] = 1; });

  // 再生時間トラッキング: 実際に聴いた長さをアーティスト/ジャンル別に積算し、おすすめに反映する
  var listenDirty = false, listenFlushAcc = 0;
  function loadListen() {
    var v = loadLS(LS_LISTEN);
    if (v && v.a && v.b) return v;     // 既存データ
    return { a: {}, b: {} };
  }
  function saveListen() { saveLS(LS_LISTEN, state.listen); }
  // 現在の曲を sec 秒ぶん聴いた、として記録(リード名義+ジャンルに加算)
  function accrueListen(t, sec) {
    if (!t || !(sec > 0) || sec > 2) return;   // 異常値(タブ復帰時の巨大dt等)は無視
    var a = leadArtist(t.artistName).toLowerCase();
    var b = t.bucket || bucketOf(t);
    state.listen.a[a] = (state.listen.a[a] || 0) + sec;
    state.listen.b[b] = (state.listen.b[b] || 0) + sec;
    listenDirty = true;
  }

  // レコード回転(JS駆動。手回しスクラッチと角度を共有するため CSS animation ではなく JS で回す)
  var discAngle = 0;
  var rafLast = 0;
  var reduceMotion = !!(window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches);
  var lyricsCache = {};   // trackId -> 歌詞テキスト(取得済みキャッシュ)


  /* ---------- DOM参照 ---------- */
  var els = {};
  var audio = new Audio();
  audio.preload = "auto";
  audio.loop = true;                       // プレビューが終わったら同じ曲をくり返し再生
  audio.setAttribute("playsinline", "");
  var audioSeq = 0;        // play()競合をガードする世代番号
  var lastErrSkip = 0;

  /* ---------- 再生エンジン ----------
     "preview": iTunesの公式30秒プレビュー(<audio>)。未連携/未契約はこちら。
     "mk":      Apple Music(MusicKit)で本編フル再生。連携かつ契約者のみ。
     MusicKit再生に失敗したら自動でpreviewへフォールバックする。 */
  var engine = "preview";
  function mkInstance() { return (window.MusicKit && MusicKit.getInstance && MusicKit.getInstance()) || null; }
  function useMK() { return engine === "mk" && state.appleConnected && !!mkInstance(); }

  /* ---------- 起動 ---------- */
  // DOMContentLoaded を取りこぼしてもよいよう、読み込み済みなら即実行する
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }

  function init() {
    cacheEls();
    guardIOS();
    bindUI();
    updateCounts();
    updateAppleConnectUI();
    applyAutoSkip();
    els.startBtn.disabled = true;
    requestAnimationFrame(animLoop);     // プログレスリングを滑らかに更新するループを開始



    loadPool().then(function (pool) {
      if (!pool.length) {
        setStatus("楽曲を取得できませんでした。通信環境をご確認ください。");
        return;
      }
      state.tracks = pool;
      buildOrder();
      loadCurrent(false);                 // 1曲目をUIに用意(音はまだ:iOSは要ユーザー操作)
      setStatus(pool.length + "曲を準備しました");
      els.startBtn.disabled = false;
    });
  }

  function cacheEls() {
    [
      "bg", "stage", "card", "disc", "artwork", "ringProgress", "tonearm",
      "trackName", "artistName", "genreTag", "genreBar",
      "prevBtn", "playBtn", "nextBtn",
      "autoSkipBtn", "libraryBtn", "libCount", "libraryPanel", "libraryClose",
      "favList", "appleList", "appleSection", "appleConnectBtn", "appleConnectNote", "favCount", "appleCount",
      "lyricsBtn", "lyricsPanel", "lyricsClose", "lyricsTitle", "lyricsArtist", "lyricsBody",
      "openApple", "toast", "startOverlay", "startBtn", "startStatus"
    ].forEach(function (id) { els[id] = document.getElementById(id); });
    els.badgeLike = document.querySelector(".badge-like");
    els.badgeNope = document.querySelector(".badge-nope");
    els.badgeUp   = document.querySelector(".badge-up");
    els.badgeDown = document.querySelector(".badge-down");
  }

  /* =========================================================
     データ読み込み
     1) ローカルにプールした musics.json (サーバ配信時)
     2) 失敗時(file://等)は iTunes API を JSONP でライブ取得(CORS回避)
     ========================================================= */
  function loadPool() {
    setStatus("楽曲を準備中…");
    // no-cache: 保存はするが毎回サーバーへ更新確認(If-Modified-Since)。変わってなければ
    // 304(本体15MBは送られず)→ モバイル通信を大幅節約。更新時はファイル日時が変わり自動で最新取得。
    return fetch("musics.json", { cache: "no-cache" })
      .then(function (res) { return res.ok ? res.json() : null; })
      .then(function (data) {
        var norm = normalize(data);
        if (norm.length) return norm;
        return loadViaJsonp();
      })
      .catch(function () {
        setStatus("オンラインで楽曲を取得中…");
        return loadViaJsonp();
      });
  }

  function normalize(arr) {
    if (!arr || !arr.length) return [];
    var seen = {}, out = [];
    for (var i = 0; i < arr.length; i++) {
      var r = arr[i];
      var preview = r.previewUrl;
      if (!preview) continue;
      var id = r.id || r.trackId || preview;
      if (seen[id]) continue;
      seen[id] = 1;
      var art = r.artwork || upgradeArt(r.artworkUrl100) || r.artworkSmall || "";
      out.push({
        id: id,
        trackName: r.trackName || "(不明な曲)",
        artistName: r.artistName || "(不明なアーティスト)",
        previewUrl: preview,
        artwork: art,
        artworkSmall: r.artworkSmall || r.artworkUrl100 || art,
        genre: r.genre || r.primaryGenreName || "",
        bucket: r.bucket || bucketOf(r),       // 主ジャンル(均等化/おすすめの集計に使用)
        buckets: r.buckets || [r.bucket || bucketOf(r)], // 所属チップ(複数可。例: アニソン＋J-POP)
        hit: !!r.hit,                          // 有名曲フラグ(約10曲に1曲挟んで飽きさせない)
        trackViewUrl: r.trackViewUrl || ""
      });
    }
    return out;
  }

  function upgradeArt(u) { return u ? u.replace("100x100bb", "600x600bb") : u; }

  function loadViaJsonp() {
    var terms = [
      ["US", "pop"], ["US", "rock"], ["US", "hip hop"], ["US", "jazz"],
      ["US", "electronic"], ["US", "r&b soul"], ["US", "classical"], ["US", "country"],
      ["US", "indie"], ["US", "metal"], ["US", "k-pop"], ["JP", "J-POP"],
      ["JP", "アニメ"], ["US", "latin"], ["US", "reggae"], ["US", "funk"]
    ];
    var all = [];
    var chain = Promise.resolve();
    terms.forEach(function (t) {
      chain = chain.then(function () {
        var url = "https://itunes.apple.com/search?term=" + encodeURIComponent(t[1]) +
          "&media=music&entity=song&limit=60&country=" + t[0];
        return jsonp(url).then(function (results) {
          for (var i = 0; i < results.length; i++) {
            if (results[i].previewUrl) all.push(results[i]);
          }
          setStatus("オンラインで楽曲を取得中… " + all.length + "曲");
        });
      });
    });
    return chain.then(function () { return normalize(all); });
  }

  function jsonp(url) {
    return new Promise(function (resolve) {
      var cb = "__itunes_cb_" + Math.random().toString(36).slice(2);
      var s = document.createElement("script");
      var done = false;
      function cleanup() { try { delete window[cb]; } catch (e) { window[cb] = undefined; } if (s.parentNode) s.parentNode.removeChild(s); }
      window[cb] = function (data) { done = true; cleanup(); resolve((data && data.results) || []); };
      s.onerror = function () { if (!done) { cleanup(); resolve([]); } };
      s.src = url + (url.indexOf("?") >= 0 ? "&" : "?") + "callback=" + cb;
      document.head.appendChild(s);
      setTimeout(function () { if (!done) { cleanup(); resolve([]); } }, 9000);
    });
  }

  /* =========================================================
     再生列(プレイリスト)管理 — シャッフルし、末尾に達したら継ぎ足して無限化
     ========================================================= */
  // 曲のジャンルバケット判定(プールに bucket が無い場合はジャンル名から推定)
  function hasJapanese(s) { return /[぀-ヿ㐀-鿿ｦ-ﾟ]/.test(s || ""); }
  function looksVocaloid(t) {
    var s = ((t.trackName || "") + " " + (t.artistName || "") + " " + (t.collectionName || "")).toLowerCase();
    return /初音ミク|hatsune miku|miku|鏡音|kagamine|巡音|megurine|重音テト|vocaloid|ボーカロイド|ボカロ|可不|音街ウナ|ずんだもん|megpoid|synthesizer v|cevio/.test(s);
  }
  function bucketOf(t) {
    if (t.bucket) return t.bucket;               // プール済みデータはbucketをそのまま使う
    var g = (t.genre || "").toLowerCase();
    if (looksVocaloid(t)) return "jpop";         // ボカロはJ-POPに統合
    if (g.indexOf("k-pop") >= 0) return "kpop";
    if (g.indexOf("j-pop") >= 0 || g.indexOf("j-rock") >= 0 || g.indexOf("anime") >= 0) return "jpop"; // アニメもJ-POPへ
    if (g.indexOf("hip") >= 0 || g.indexOf("rap") >= 0) {
      return hasJapanese((t.artistName || "") + (t.trackName || "")) ? "hiphop_jp" : "hiphop_us";
    }
    if (g.indexOf("classical") >= 0 || g.indexOf("soundtrack") >= 0 ||
        g.indexOf("jazz") >= 0 || g.indexOf("ambient") >= 0) return "bgm";
    return "yougaku";
  }

  function bucketsOf(t) { return t.buckets || [bucketOf(t)]; }   // 所属チップ(複数可)

  function poolForBucket() {
    if (state.bucket === "all") return state.tracks;
    var b = state.bucket;
    return state.tracks.filter(function (t) { return bucketsOf(t).indexOf(b) >= 0; });
  }

  // 全ジャンル均等になるよう、バケットごとにグループ化して総当たりで1曲ずつ取り出す。
  // → 海外曲が連続せず、ジャンルが入り混じった「もっとランダム」な並びになる。
  function balancedOrder(tracks) {
    var groups = {};
    tracks.forEach(function (t) {
      var b = bucketOf(t);
      (groups[b] = groups[b] || []).push(t);
    });
    var keys = Object.keys(groups);
    keys.forEach(function (k) { groups[k] = soloFirst(shuffle(groups[k])); }); // ソロ曲を先に出す
    var pos = {};
    keys.forEach(function (k) { pos[k] = 0; });
    var out = [], added = true;
    while (added) {
      added = false;
      var round = shuffle(keys.slice());           // 毎ラウンド順番を入れ替えてさらにばらす
      for (var i = 0; i < round.length; i++) {
        var k = round[i], g = groups[k];
        if (pos[k] < g.length) { out.push(g[pos[k]]); pos[k]++; added = true; }
      }
    }
    return out;
  }

  // 「あなたへのおすすめ」: お気に入り(右スワイプでキープした曲)から好みを学習して並べ替える。
  // 同じアーティスト・好きなジャンルを強めに、少しランダムも混ぜる。履歴が無ければ均等ランダム。
  // 「あなたへのおすすめ」: お気に入りから“好きなジャンル/アーティスト”を学習しつつ、
  // アーティストを総当たりで1曲ずつ出す → 特定の人(例:Stray Kids)に偏らず、好きな系統の
  // いろんなアーティストが流れる。各アーティスト内は未聴を優先。
  function recommendedOrder() {
    var favs = state.fav || [];
    // (1) いいね(右/左スワイプでキープ)から好みのジャンル・アーティストを集計
    var bucketScore = {}, artistSet = {};
    favs.forEach(function (f) {
      var b = f.bucket || bucketOf(f);
      bucketScore[b] = (bucketScore[b] || 0) + 1;
      artistSet[leadArtist(f.artistName || "").toLowerCase()] = true;   // リード名義で照合
    });
    var maxB = 1;
    for (var k in bucketScore) if (bucketScore[k] > maxB) maxB = bucketScore[k];

    // (2) 実際に聴いた時間(再生時間)を集計 → 長く聴いたアーティスト/ジャンルほど重視
    var la = (state.listen && state.listen.a) || {}, lb = (state.listen && state.listen.b) || {};
    var maxLA = 1, maxLB = 1;
    for (var ka in la) if (la[ka] > maxLA) maxLA = la[ka];
    for (var kb in lb) if (lb[kb] > maxLB) maxLB = lb[kb];

    var groups = {}, keys = [];
    for (var i = 0; i < state.tracks.length; i++) {
      var t = state.tracks[i], a = leadArtist(t.artistName);   // コラボはリードにまとめる
      if (!groups[a]) { groups[a] = []; keys.push(a); }
      groups[a].push(t);
    }
    keys.forEach(function (a) { groups[a] = soloFirst(freshFirst(shuffle(groups[a]))); }); // 未聴かつソロ優先

    // アーティストの“おすすめ度” = 好きなジャンル + 好きなアーティスト + よく聴くジャンル/アーティスト。
    // ただし固定順にすると毎回同じ曲が先頭に来るので「重み付きシャッフル」にする:
    // スコアが高いほど前に来やすいが、ランダム係数で起動のたびに順番が変わる。
    var sc = {};
    keys.forEach(function (a) {
      var b0 = bucketOf(groups[a][0]), al = a.toLowerCase();
      var s = (bucketScore[b0] || 0) / maxB * 2;             // いいねの多いジャンル (0〜2)
      if (artistSet[al]) s += 5;                             // いいねしたアーティストを強く優先
      s += (lb[b0] || 0) / maxLB * 2;                        // よく聴くジャンル(再生時間) (0〜2)
      s += (la[al] || 0) / maxLA * 2.5;                      // よく聴くアーティスト(再生時間) (0〜2.5)
      sc[a] = (s + 0.5) * (0.6 + Math.random() * 0.8);       // ×ランダム(好み寄りを維持しつつ多少ばらす)
    });
    keys.sort(function (x, y) { return sc[y] - sc[x]; });

    // アーティスト総当たりで多彩な土台を作る(1巡で全アーティストが1回ずつ)
    var base = [], pos = {};
    keys.forEach(function (a) { pos[a] = 0; });
    var active = true;
    while (active) {
      active = false;
      for (var j = 0; j < keys.length; j++) {
        var g = groups[keys[j]];
        if (pos[keys[j]] < g.length) { base.push(g[pos[keys[j]]]); pos[keys[j]]++; active = true; }
      }
    }
    // いいねしたアーティストの曲を一定間隔で織り込み、おすすめ内で頻繁に流れるようにする。
    // (全アーティスト総当たりだと埋もれてしまうため、お気に入り枠を別に確保する)
    return favSpacing(base, artistSet);
  }

  // いいねしたアーティストの曲を約3曲に1曲の割合で差し込む(残りは未開拓の発見枠)。
  // お気に入りアーティストの曲が尽きたら通常曲のみ続行。順序(未聴/おすすめ度)は保つ。
  function favSpacing(order, artistSet) {
    if (!artistSet) return order;
    var favs = [], rest = [];
    for (var i = 0; i < order.length; i++) {
      var a = leadArtist(order[i].artistName).toLowerCase();
      (artistSet[a] ? favs : rest).push(order[i]);
    }
    if (!favs.length || !rest.length) return order;
    var out = [], fi = 0, ri = 0, GAP = 2;        // 通常2曲ごとにお気に入り1曲 → 約1/3が好きな人
    while (fi < favs.length || ri < rest.length) {
      if (fi < favs.length) out.push(favs[fi++]);  // 先頭はお気に入りから
      for (var c = 0; c < GAP && ri < rest.length; c++) out.push(rest[ri++]);
    }
    return out;
  }

  function makeOrder() {
    // soloBias: ソロ曲を主役に / hitSpacing: 約10曲に1曲は有名曲(飽き防止)。
    // おすすめは学習した好みだけで並べる(有名曲の定期挿入はしない)。
    if (state.bucket === "osusume") return soloBias(recommendedOrder());
    var pool = poolForBucket();
    if (state.bucket === "all") return hitSpacing(soloBias(deCluster(freshFirst(balancedOrder(pool)))));
    // 特定ジャンル: アーティストを総当たりで1曲ずつ出す → 多作な人に偏らず、いろんな人が出る
    var ord = artistRoundRobin(freshFirst(shuffle(pool.slice())));
    if (COLLAB_OK[state.bucket]) ord = spreadParticipants(ord, 8); // 客演含めて散らす(連続感を消す)
    else ord = soloBias(ord);                            // コラボ主流ジャンル以外はソロ寄せ
    return hitSpacing(ord);
  }

  // アーティストを総当たり(round-robin)で1曲ずつ並べる。多作なアーティストに偏らず、
  // 1巡目で全アーティストが1回ずつ出るので“いろんなアーティスト”が流れる（曲は減らさない）。
  function artistRoundRobin(order) {
    if (order.length < 3) return order;
    var groups = {}, keys = [];
    for (var i = 0; i < order.length; i++) {
      var a = leadArtist(order[i].artistName);   // コラボはリードアーティストにまとめる
      if (!groups[a]) { groups[a] = []; keys.push(a); }
      groups[a].push(order[i]);          // 各アーティスト内は freshFirst の順(未聴優先)を保持
    }
    if (!COLLAB_OK[state.bucket])         // コラボ主流ジャンルではソロ優先しない
      keys.forEach(function (a) { groups[a] = soloFirst(groups[a]); }); // 各アーティスト内はソロ曲優先
    shuffle(keys);                       // アーティストの巡回順はランダムに
    // 巡回リスト。ブースト対象は均等な位置に複製を挿入し、1巡あたりの出現回数を増やす
    var rotation = keys.slice();
    for (var bk = 0; bk < keys.length; bk++) {
      var w = ARTIST_BOOST[keys[bk]] || 1;
      for (var m = 1; m < w; m++) {
        rotation.splice(Math.floor(rotation.length * m / w), 0, keys[bk]);
      }
    }
    var out = [], pos = {};
    for (var k = 0; k < keys.length; k++) pos[keys[k]] = 0;
    var active = true;
    while (active) {
      active = false;
      for (var j = 0; j < rotation.length; j++) {
        var a = rotation[j], g = groups[a];
        if (pos[a] < g.length) { out.push(g[pos[a]]); pos[a]++; active = true; }
      }
    }
    return out;
  }

  // 同じアーティストが連続しないよう並べ替える（曲は減らさない）。
  // 元の優先順(新しさ/おすすめ度)はできるだけ保ちつつ、直前と同じアーティストを避ける。
  function deCluster(order) {
    var n = order.length;
    if (n < 3) return order;
    var used = new Uint8Array(n);
    var result = new Array(n);
    var last = "";
    var start = 0;
    for (var k = 0; k < n; k++) {
      while (start < n && used[start]) start++;
      var pick = -1, scanned = 0;
      for (var i = start; i < n && scanned < 220; i++) {
        if (used[i]) continue;
        scanned++;
        if ((order[i].artistName || "") !== last) { pick = i; break; }
      }
      if (pick < 0) pick = start;            // 残りが全部同じアーティストならそのまま
      used[pick] = 1;
      result[k] = order[pick];
      last = order[pick].artistName || "";
    }
    return result;
  }

  // 最近再生した曲を後ろへ回し、まだ聴いていない曲を先に流す → 起動のたびに違う流れになる
  function freshFirst(order) {
    if (!state.seen.length) return order;
    // 再生済みの「新しさ」ランク(配列の後ろほど最近再生した曲)
    var rank = {};
    for (var k = 0; k < state.seen.length; k++) rank[state.seen[k]] = k;
    var fresh = [], old = [];
    for (var i = 0; i < order.length; i++) {
      if (state.seenSet[order[i].id]) old.push(order[i]); else fresh.push(order[i]);
    }
    // 未聴を先に。再生済みは「最近聴いた曲ほど後ろ」に並べ、直近の曲ほど再登場しにくくする
    old.sort(function (a, b) { return (rank[a.id] || 0) - (rank[b.id] || 0); });
    return fresh.concat(old);
  }

  function markSeen(id) {
    if (id == null || state.seenSet[id]) return;
    state.seen.push(id);
    state.seenSet[id] = 1;
    if (state.seen.length > SEEN_CAP) { var rem = state.seen.shift(); delete state.seenSet[rem]; }
    saveLS(LS_SEEN, state.seen);
  }

  function buildOrder() {
    state.order = makeOrder();
    state.pos = 0;
  }
  function currentTrack() { return state.order[state.pos]; }

  function gotoNext() {
    state.pos++;
    if (state.pos >= state.order.length) {
      var more = makeOrder();
      var last = state.order[state.order.length - 1];
      if (more.length > 1 && last && more[0].id === last.id) more.push(more.shift());
      state.order = state.order.concat(more);
    }
    loadCurrent(true);
  }
  function gotoPrev() {
    if (state.pos > 0) state.pos--;
    loadCurrent(true);
  }

  // ジャンルチップ選択
  function selectBucket(b) {
    if (state.bucket === b) return;
    var pool = (b === "all" || b === "osusume")
      ? state.tracks
      : state.tracks.filter(function (t) { return bucketsOf(t).indexOf(b) >= 0; });
    if (!pool.length) { toast("この曲がまだありません"); return; }
    state.bucket = b;
    var chips = els.genreBar.querySelectorAll(".chip");
    for (var i = 0; i < chips.length; i++) {
      chips[i].classList.toggle("is-active", chips[i].getAttribute("data-bucket") === b);
    }
    buildOrder();
    loadCurrent(state.started);                    // 新ジャンルの1曲目を即再生
    toast(chipLabel(b) + " に切り替え");
  }
  function chipLabel(b) {
    var map = { osusume: "あなたへのおすすめ", all: "すべて", jpop: "J-POP", kpop: "K-POP",
      yougaku: "洋楽", hiphop_jp: "HIPHOP(JP)", hiphop_us: "HIPHOP(US)",
      vocaloid: "ボカロ", anime: "アニソン", bgm: "BGM" };
    return map[b] || b;
  }

  /* =========================================================
     現在曲の描画 + オーディオ
     ========================================================= */
  function loadCurrent(autoplay) {
    var t = currentTrack();
    if (!t) return;
    markSeen(t.id);                       // 再生済みとして記録(次回以降は後回し)
    els.trackName.textContent = t.trackName;
    els.artistName.textContent = t.artistName;
    els.genreTag.textContent = t.genre || "";
    els.genreTag.style.display = t.genre ? "" : "none";
    setAppleLink(t);                      // 「Apple Musicで開く」導線を更新
    setArtwork(t);
    setRing(0);
    if (useMK()) loadMK(t, autoplay);     // 連携・契約者は本編フル再生
    else loadAudio(t, autoplay);          // それ以外は公式30秒プレビュー
    preloadNext();
  }

  // 各曲を Apple Music で開くリンク(誘導導線)。trackViewUrl が無ければ曲IDから組み立てる。
  function setAppleLink(t) {
    if (!els.openApple) return;
    var url = t.trackViewUrl || (t.id ? "https://music.apple.com/jp/song/" + t.id : "");
    if (url) { els.openApple.href = url; els.openApple.classList.remove("hidden"); }
    else { els.openApple.classList.add("hidden"); }
  }

  // MusicKitで本編をキュー＆再生。失敗時はプレビューへフォールバック。
  function loadMK(t, autoplay) {
    var my = ++audioSeq;
    try { audio.pause(); } catch (e) {}                 // プレビュー側は止める
    var music = mkInstance();
    if (!music) { engine = "preview"; loadAudio(t, autoplay); return; }
    setPlaying(false);
    Promise.resolve(music.setQueue({ song: String(t.id) })).then(function () {
      if (my !== audioSeq) return;                      // 既に次の曲へ移っていたら無視
      if (autoplay && state.started) return music.play();
    }).then(function () {
      if (my === audioSeq && autoplay && state.started) setPlaying(true);
    }).catch(function (err) {
      if (window.console) console.warn("MusicKit再生に失敗 → プレビューに切替", err);
      if (my === audioSeq) { engine = "preview"; loadAudio(t, autoplay); }  // フォールバック
    });
  }

  function setArtwork(t) {
    var img = els.artwork;
    img.onerror = function () { img.onerror = null; if (t.artworkSmall) img.src = t.artworkSmall; };
    img.src = t.artwork || t.artworkSmall || "";
    var bgUrl = t.artwork || t.artworkSmall || "";
    els.bg.style.backgroundImage = bgUrl ? 'url("' + bgUrl + '")' : "none";
  }

  function preloadNext() {
    var nx = state.order[state.pos + 1];
    if (nx && nx.artwork) { var im = new Image(); im.src = nx.artwork; }
  }

  function loadAudio(t, autoplay) {
    var my = ++audioSeq;
    try { audio.pause(); } catch (e) {}
    try { audio.playbackRate = 1; } catch (e) {}   // 倍速の取り残しをリセット
    audio.src = t.previewUrl;
    try { audio.currentTime = 0; } catch (e) {}
    if (autoplay && state.started) {
      var p = audio.play();
      if (p && p.then) {
        p.then(function () { if (my === audioSeq) setPlaying(true); })
         .catch(function () { /* 自動再生ブロック/読み込み中断は無視 */ });
      }
    } else {
      setPlaying(false);
    }
  }

  function setPlaying(on) {
    state.playing = on;
    els.tonearm.classList.toggle("on", on);
    els.playBtn.classList.toggle("playing", on);
  }

  // 毎フレーム: 再生中(かつ手回し中でない)はレコードを少しずつ回し、リングを滑らかに更新する。
  // 手回しスクラッチ中は onMove 側が discAngle と currentTime を直接動かすのでここはスキップ。
  function animLoop(ts) {
    if (!rafLast) rafLast = ts;
    var dt = ts - rafLast;
    rafLast = ts;
    if (!state.scrubbing) {
      if (state.playing) {
        if (!reduceMotion) {
          discAngle = (discAngle + dt * ROT_DEG_PER_MS) % 360;
          els.disc.style.transform = "rotate(" + discAngle + "deg)";
        }
        accrueListen(currentTrack(), dt / 1000);   // 実際に聴いた時間を学習に積算
        listenFlushAcc += dt;
        if (listenDirty && listenFlushAcc > 8000) { saveListen(); listenDirty = false; listenFlushAcc = 0; }
      }
      var cur, d;
      if (useMK()) { var m = mkInstance(); cur = m.currentPlaybackTime || 0; d = m.currentPlaybackDuration || 0; }
      else { cur = audio.currentTime; d = audio.duration || 30; }
      if (d > 0) setRing(cur / d);
    }
    requestAnimationFrame(animLoop);
  }

  function togglePlay() {
    if (!state.started) return;
    if (useMK()) {                                   // MusicKit本編再生の再生/停止
      var music = mkInstance();
      if (music.isPlaying) { music.pause(); setPlaying(false); }
      else { Promise.resolve(music.play()).then(function () { setPlaying(true); }).catch(function () {}); }
      return;
    }
    if (audio.paused) {
      if (audio.ended) { try { audio.currentTime = 0; } catch (e) {} setRing(0); } // 終わってたら頭から
      var p = audio.play();
      if (p && p.then) p.then(function () { setPlaying(true); }).catch(function () {});
      else setPlaying(true);
    } else {
      audio.pause();
      setPlaying(false);
    }
  }

  function setRing(frac) {
    els.ringProgress.style.strokeDashoffset = RING_LEN * (1 - Math.max(0, Math.min(1, frac)));
  }

  // オーディオイベント（リング更新は基本 animLoop、これは保険のフォールバック）
  audio.addEventListener("timeupdate", function () {
    var d = audio.duration || 30;
    if (d > 0) setRing(audio.currentTime / d);
  });
  // 30秒の試聴が終わっても自動で次へ行かず、その曲のまま停止する
  audio.addEventListener("ended", function () {
    if (state.autoSkip) { softNext(); return; }     // 自動スキップON → 次の曲へ
    // OFF: 同じ曲をくり返す（loop=trueなら通常ここは呼ばれない。loop非対応環境の保険）
    try { audio.currentTime = 0; } catch (e) {}
    setRing(0);
    var p = audio.play();
    if (p && p.then) p.then(function () { setPlaying(true); }).catch(function () {});
  });

  // 自動スキップの反映: ONなら loop を切って ended→次へ、OFFなら loop でくり返し
  function applyAutoSkip() {
    audio.loop = !state.autoSkip;
    if (!els.autoSkipBtn) return;
    els.autoSkipBtn.classList.toggle("on", state.autoSkip);
    els.autoSkipBtn.setAttribute("aria-pressed", state.autoSkip ? "true" : "false");
  }
  function toggleAutoSkip() {
    state.autoSkip = !state.autoSkip;
    try { localStorage.setItem("discoSwipe.autoSkip", state.autoSkip ? "1" : "0"); } catch (e) {}
    applyAutoSkip();
    toast(state.autoSkip ? "自動スキップ ON（曲が終わると次へ）" : "自動スキップ OFF（くり返し再生）");
  }
  audio.addEventListener("play", function () { setPlaying(true); });
  audio.addEventListener("pause", function () {
    if (!audio.ended) setPlaying(false);
    if (listenDirty) { saveListen(); listenDirty = false; }   // 停止時に再生時間を確定保存
  });
  // タブを閉じる/バックグラウンドへ → 未保存の再生時間を確実に保存
  window.addEventListener("pagehide", function () { if (listenDirty) { saveListen(); listenDirty = false; } });
  document.addEventListener("visibilitychange", function () {
    if (document.visibilityState === "hidden" && listenDirty) { saveListen(); listenDirty = false; }
  });
  audio.addEventListener("error", function () {
    // 稀に試聴URLが失効していることがある。連続失敗ループを避けつつ次へ。
    if (!state.started) return;
    var now = Date.now();
    if (now - lastErrSkip < 1500) return;
    lastErrSkip = now;
    softNext();
  });

  /* =========================================================
     スワイプ操作(Pointer Events で touch/mouse 統一)
     ========================================================= */
  var drag = null;
  var scrubHintShown = false;

  function discCenter() {
    var r = els.disc.getBoundingClientRect();
    return { cx: r.left + r.width / 2, cy: r.top + r.height / 2, r: r.width / 2 };
  }
  function angleAt(x, y, c) { return Math.atan2(y - c.cy, x - c.cx) * 180 / Math.PI; }
  function normDeg(d) { while (d > 180) d -= 360; while (d < -180) d += 360; return d; }

  // 操作の判定方針（スマホでスワイプが手回しに化けないように）:
  //   ・指が少しでも動いたら即「スワイプ」確定 → スキップ/キープ/プレイリストは常に確実に効く
  //   ・ほぼ動かさず SCRUB_HOLD_MS だけ長押しすると「手回し(スクラッチ)」モードに入り、回すと早送り/巻き戻し
  //   ・ほぼ動かさず素早く離す＝タップ(再生/停止)
  function onDown(e) {
    if (state.locked || !state.started) return;
    var c = discCenter();
    drag = {
      x0: e.clientX, y0: e.clientY, dx: 0, dy: 0,
      isSwipe: false, scrub: false, speed: false, holdTimer: null,
      t0: Date.now(), c: c,
      startRadius: Math.sqrt(Math.pow(e.clientX - c.cx, 2) + Math.pow(e.clientY - c.cy, 2)),
      lastAng: angleAt(e.clientX, e.clientY, c),
      swept: 0, lastSwept: 0, scrubStartSwept: 0
    };
    els.card.classList.remove("animating");
    drag.holdTimer = setTimeout(enterScrub, SCRUB_HOLD_MS);   // 長押し→手回し
    if (e.pointerId != null && els.stage.setPointerCapture) {
      try { els.stage.setPointerCapture(e.pointerId); } catch (_) {}
    }
  }

  function onMove(e) {
    if (!drag) return;
    if (e.cancelable) e.preventDefault();
    drag.dx = e.clientX - drag.x0;
    drag.dy = e.clientY - drag.y0;

    // 回転角の積算（手回し時に使用。中心付近は角度が暴れるので半径30px以上のみ）
    var c = drag.c;
    var radius = Math.sqrt(Math.pow(e.clientX - c.cx, 2) + Math.pow(e.clientY - c.cy, 2));
    var ang = angleAt(e.clientX, e.clientY, c);
    if (radius > 30) drag.swept += normDeg(ang - drag.lastAng);
    drag.lastAng = ang;

    if (drag.speed) return;   // 2倍速モード中は他の操作にしない(指を多少動かしても維持)

    // 未確定: 少しでも動いたら「スワイプ」に確定（長押しタイマー解除＝手回しに化けない）
    if (!drag.scrub && !drag.isSwipe) {
      if (Math.sqrt(drag.dx * drag.dx + drag.dy * drag.dy) > SWIPE_MIN_MOVE) {
        drag.isSwipe = true;
        if (drag.holdTimer) { clearTimeout(drag.holdTimer); drag.holdTimer = null; }
        els.card.classList.add("dragging");
      } else {
        return;   // まだ判定待ち（長押し成立を待つ）
      }
    }

    if (drag.isSwipe) {
      var isVert = Math.abs(drag.dy) > Math.abs(drag.dx);
      var mx, my, rot;
      if (isVert) {
        mx = drag.dx * 0.08; my = drag.dy; rot = 0;
      } else {
        mx = drag.dx; my = drag.dy * 0.12; rot = clamp(drag.dx / 18, -16, 16);
      }
      setCardTransform(mx, my, rot);
      updateBadges(drag.dx, drag.dy);
      return;
    }

    // 手回し中: レコードを指に追従して回し、回した分だけ曲位置を移動
    var rel = drag.swept - drag.scrubStartSwept;
    var dSwept = drag.swept - drag.lastSwept;
    drag.lastSwept = drag.swept;
    discAngle = drag.scrubBaseAngle + rel;
    els.disc.style.transform = "rotate(" + discAngle + "deg)";
    var dur = audio.duration || 30;
    var t = clamp(drag.scrubBaseTime + rel * SEC_PER_DEG, 0, dur);
    try { audio.currentTime = t; } catch (_) {}
    setRing(t / dur);
    updateScratch(dSwept);                  // 時計回り=早送り / 反時計回り=巻き戻し音
  }

  // 長押し成立 → レコードの外なら2倍速、レコード上なら手回し(スクラッチ)
  function enterScrub() {
    if (!drag || drag.isSwipe || drag.scrub || drag.speed) return;
    if (useMK()) return;   // 手回し/2倍速はプレビュー専用ギミック。本編再生中は無効
    drag.holdTimer = null;
    if (drag.startRadius > drag.c.r) { enterSpeed(); return; }  // レコードの無い場所=2倍速
    drag.scrub = true;
    state.scrubbing = true;
    drag.scrubStartSwept = drag.swept;
    drag.scrubBaseTime = audio.currentTime || 0;
    drag.scrubBaseAngle = discAngle;
    drag.lastSwept = drag.swept;
    drag.scrubWasPlaying = !audio.paused;
    try { audio.pause(); } catch (_) {}      // 手回し中は本来の音を止め、スクラッチ音を鳴らす
    startScratch();
    haptic();
    if (!scrubHintShown) { toast("手回しモード：回して早送り/巻き戻し"); scrubHintShown = true; }
  }

  // レコードの外を長押し → 2倍速モードに入る
  function enterSpeed() {
    if (drag.holdTimer) { clearTimeout(drag.holdTimer); drag.holdTimer = null; }
    if (drag.scrub) { drag.scrub = false; state.scrubbing = false; stopScratch(); }
    drag.isSwipe = false;
    drag.speed = true;
    els.card.classList.remove("dragging");
    try { audio.playbackRate = SPEED_RATE; } catch (_) {}
    if (audio.paused) {                        // 止まっていたら倍速で再生開始
      var p = audio.play();
      if (p && p.then) p.then(function () { setPlaying(true); }).catch(function () {});
      else setPlaying(true);
    }
    haptic2x();                     // 2倍速にした触覚フィードバック(iOS/Android両対応)
    var st = document.getElementById("speedTag"); if (st) st.classList.add("show");
  }
  function exitSpeed() {
    try { audio.playbackRate = 1; } catch (_) {}
    var st = document.getElementById("speedTag"); if (st) st.classList.remove("show");
  }

  function onUp() {
    if (!drag) return;
    var d = drag;
    drag = null;
    if (d.holdTimer) { clearTimeout(d.holdTimer); d.holdTimer = null; }

    if (d.speed) {                           // 2倍速モード終了 → 通常速度に戻す
      exitSpeed();
      snapBack();
      return;
    }

    if (d.scrub) {                           // 手回し終了 → その位置から再生を再開
      state.scrubbing = false;
      stopScratch();
      if (d.scrubWasPlaying) {
        var p = audio.play();
        if (p && p.then) p.then(function () { setPlaying(true); }).catch(function () {});
        else setPlaying(true);
      }
      return;
    }

    els.card.classList.remove("dragging");
    var dist = Math.sqrt(d.dx * d.dx + d.dy * d.dy);
    var dt = Math.max(1, Date.now() - d.t0);
    if (d.isSwipe) {
      var vx = d.dx / dt, vy = d.dy / dt, action = null;
      var isVert = Math.abs(d.dy) > Math.abs(d.dx);
      if (isVert) {
        if (d.dy < -SWIPE_DIST || vy < -SWIPE_VEL) action = "next";   // 上スワイプ=次の曲
        else if (d.dy > SWIPE_DIST || vy > SWIPE_VEL) action = "prev"; // 下スワイプ=前の曲
      } else {
        if (Math.abs(d.dx) > SWIPE_DIST || Math.abs(vx) > SWIPE_VEL) action = "like"; // 左右=いいね
      }
      if (action) commit(action); else snapBack();
      return;
    }
    // 動かさず長押しもせず離した → タップ。1回=再生/停止 / 2回連続=いいね
    if (dist < TAP_DIST && dt < TAP_MS) handleTap();
    else snapBack();
  }

  // シングルタップ=再生/停止、ダブルタップ=いいね。
  // 2回目を待つため少し遅らせてからシングルを実行する（ダブル時はキャンセル）。
  var tapTimer = null;
  function handleTap() {
    if (tapTimer) {                 // 2回目 → ダブルタップ＝いいね（曲は飛ばさない）
      clearTimeout(tapTimer); tapTimer = null;
      likeCurrent();
      return;
    }
    tapTimer = setTimeout(function () { tapTimer = null; togglePlay(); }, 250);
  }

  /* ---------- レコードを戻す音(スクラッチ): Web Audioで合成 ---------- */
  var actx = null, scratchNoise = null, scratchSrc = null, scratchGain = null, scratchFilter = null;

  function ensureAudioCtx() {
    if (actx) return;
    var AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return;
    actx = new AC();
    var len = Math.floor(actx.sampleRate * 1.2);
    scratchNoise = actx.createBuffer(1, len, actx.sampleRate);
    var data = scratchNoise.getChannelData(0);
    for (var i = 0; i < len; i++) data[i] = Math.random() * 2 - 1;   // ホワイトノイズ
  }
  function startScratch() {
    ensureAudioCtx(); if (!actx) return;
    if (actx.state === "suspended") { try { actx.resume(); } catch (e) {} }
    stopScratch();
    scratchSrc = actx.createBufferSource();
    scratchSrc.buffer = scratchNoise; scratchSrc.loop = true;
    scratchFilter = actx.createBiquadFilter();
    scratchFilter.type = "bandpass"; scratchFilter.frequency.value = 600; scratchFilter.Q.value = 1.1;
    scratchGain = actx.createGain(); scratchGain.gain.value = 0;
    scratchSrc.connect(scratchFilter); scratchFilter.connect(scratchGain); scratchGain.connect(actx.destination);
    try { scratchSrc.start(); } catch (e) {}
  }
  function updateScratch(dSwept) {
    if (!actx || !scratchGain) return;
    var spd = Math.min(1, Math.abs(dSwept) / 22);   // 手回しの速さ(0..1)
    var backward = dSwept < 0;                       // 反時計回り=巻き戻し
    var now = actx.currentTime;
    scratchGain.gain.setTargetAtTime(spd * 0.3, now, 0.02);
    scratchFilter.frequency.setTargetAtTime((backward ? 320 : 760) + spd * 900, now, 0.02); // 戻しは低音
  }
  function stopScratch() {
    if (scratchGain && actx) scratchGain.gain.setTargetAtTime(0, actx.currentTime, 0.05);
    if (scratchSrc) {
      var s = scratchSrc; scratchSrc = null;
      setTimeout(function () { try { s.stop(); } catch (e) {} }, 140);
    }
  }

  function setCardTransform(x, y, rot) {
    els.card.style.transform = "translate3d(" + x + "px," + y + "px,0) rotate(" + rot + "deg)";
  }

  function updateBadges(dx, dy) {
    var horiz = Math.abs(dx) >= Math.abs(dy);
    var likeOp = horiz ? clamp(Math.abs(dx) / 110, 0, 1) : 0;
    els.badgeLike.style.opacity = (horiz && dx >= 0) ? likeOp : 0;  // 右スワイプ
    els.badgeNope.style.opacity = (horiz && dx < 0)  ? likeOp : 0;  // 左スワイプ
    els.badgeUp.style.opacity   = (!horiz && dy < 0) ? clamp(-dy / 110, 0, 1) : 0; // 上=次
    els.badgeDown.style.opacity = (!horiz && dy > 0) ? clamp(dy  / 110, 0, 1) : 0; // 下=前
  }
  function clearBadges() {
    els.badgeLike.style.opacity = 0;
    els.badgeNope.style.opacity = 0;
    els.badgeUp.style.opacity   = 0;
    els.badgeDown.style.opacity = 0;
  }

  function snapBack() {
    els.card.classList.add("animating");
    setCardTransform(0, 0, 0);
    clearBadges();
    setTimeout(function () { els.card.classList.remove("animating"); }, OUT_MS);
  }

  /* =========================================================
     カードの差し替え(フリング→内容更新→新カード登場)
     ★ iOS Safari の描画残像(ゴースト)対策:
        トランジションを一旦切ってから強制リフローを挟み、
        位置リセットがアニメーションとして再生されるのを防ぐ。
     ========================================================= */
  function swapCard(outX, outY, outRot, inX, inY, advance) {
    state.locked = true;
    var card = els.card;
    card.classList.remove("dragging");
    card.classList.add("animating");
    setCardTransform(outX, outY, outRot);
    card.style.opacity = "0";

    setTimeout(function () {
      advance();                              // posを進め、次の曲を読み込む(音はすぐ開始)
      card.classList.remove("animating");     // トランジション無効化
      setCardTransform(inX, inY, 0);
      card.style.opacity = "0";
      void card.offsetWidth;                  // ★強制リフロー(ここが肝)
      card.classList.add("animating");        // 再度有効化して「登場」だけアニメ
      setCardTransform(0, 0, 0);
      card.style.opacity = "1";
      clearBadges();
      state.locked = false;                   // 早めに解放して連打に追従
      setTimeout(function () { card.classList.remove("animating"); }, IN_MS);
    }, OUT_MS);
  }

  function commit(action) {
    if (state.locked) return;
    var h = window.innerHeight;
    if (action === "like") {                       // 左右スワイプ=いいね(曲は飛ばさず、その場でいいね)
      likeCurrent();
      snapBack();                                  // カードは元の位置に戻す（次へ進まない）
    } else if (action === "next") {                // 上スワイプ=次の曲(カードは上へ、新カードは下から)
      haptic();
      swapCard(0, -h * 1.15, 0, 0, h * 0.5, gotoNext);
    } else if (action === "prev") {                // 下スワイプ=前の曲(カードは下へ、新カードは上から)
      if (state.pos <= 0) { toast("これ以上は戻れません"); snapBack(); return; }
      haptic();
      swapCard(0, h * 1.15, 0, 0, -h * 0.5, gotoPrev);
    }
  }

  // いいね(左右スワイプ / ダブルタップ): 曲は進めず、お気に入り登録＋ハート演出だけ行う
  function likeCurrent() {
    if (!state.started) return;
    var cur = currentTrack();
    if (!cur) return;
    var already = existsIn(state.fav, cur.id);
    addFavorite(cur);
    addToAppleMusicPlaylist(cur);                  // 連携時はApple Musicプレイリストにも追加
    toast(already ? "♥ いいね済み" : "♥ いいねしました");
    haptic();
    heartBurst();
  }

  // 画面中央にハートをポンと出す演出
  function heartBurst() {
    var h = document.createElement("div");
    h.className = "heart-burst";
    h.textContent = "♥";
    els.stage.appendChild(h);
    setTimeout(function () { if (h.parentNode) h.parentNode.removeChild(h); }, 650);
  }

  function goPrev() {
    if (state.locked || !state.started) return;
    if (state.pos <= 0) { toast("これ以上は戻れません"); return; }
    haptic();
    swapCard(0, window.innerHeight * 1.15, 0, 0, -window.innerHeight * 0.5, gotoPrev);
  }

  // 次へボタン(旧:最初から再生ボタン)
  function goNext() {
    if (state.locked || !state.started) return;
    haptic();
    swapCard(0, -window.innerHeight * 1.15, 0, 0, window.innerHeight * 0.5, gotoNext);
  }

  function softNext() {                         // 30秒経過の自動送り(フェード)
    if (state.locked) return;
    swapCard(0, 0, 0, 0, 44, gotoNext);
  }

  /* =========================================================
     お気に入り / Apple Music追加リスト(localStorage永続化)
     ========================================================= */
  function addFavorite(t) {
    if (!t) return;
    if (existsIn(state.fav, t.id)) return;
    state.fav.unshift(slim(t));
    saveLS(LS_FAV, state.fav);
    updateCounts();
  }
  function addApple(t) {
    if (!t) return;
    if (!existsIn(state.apple, t.id)) {
      state.apple.unshift(slim(t));
      saveLS(LS_APPLE, state.apple);
    }
    updateCounts();
    addToAppleMusicPlaylist(t);
  }

  /* =========================================================
     Apple Music 連携（MusicKit JS）
     連携後は、上スワイプ(キープ)した曲が自動で Apple Music のプレイリスト
     「Disco Swipe」に追加される。
     ※ 連携には MusicKit の Developer Token（Apple Developerアカウントで発行）と
        Apple Music サブスクが必要。トークンは window.APPLE_DEVELOPER_TOKEN か
        localStorage(discoSwipe.appleDevToken) から読む（無ければ連携時に入力を促す）。
     ========================================================= */
  function getAppleDevToken() {
    return (window.APPLE_DEVELOPER_TOKEN || localStorage.getItem("discoSwipe.appleDevToken") || "").trim();
  }

  function ensureMusicKit() {
    return new Promise(function (resolve, reject) {
      if (window.MusicKit) { resolve(window.MusicKit); return; }
      document.addEventListener("musickitloaded", function () { resolve(window.MusicKit); }, { once: true });
      if (!document.getElementById("musickit-js")) {
        var s = document.createElement("script");
        s.id = "musickit-js";
        s.src = "https://js-cdn.music.apple.com/musickit/v3/musickit.js";
        s.setAttribute("data-web-components", "");
        s.async = true;
        s.onerror = function () { reject(new Error("MusicKitの読み込みに失敗")); };
        document.head.appendChild(s);
      }
      setTimeout(function () { window.MusicKit ? resolve(window.MusicKit) : reject(new Error("MusicKit読み込みタイムアウト")); }, 12000);
    });
  }

  function connectAppleMusic() {
    var token = getAppleDevToken();
    if (!token) {
      token = (window.prompt(
        "Apple Music連携には MusicKit の Developer Token が必要です。\n" +
        "Apple Developerアカウントで発行したトークンを貼り付けてください。"
      ) || "").trim();
      if (!token) { toast("連携をキャンセルしました"); return; }
      try { localStorage.setItem("discoSwipe.appleDevToken", token); } catch (e) {}
    }
    toast("Apple Musicに接続中…");
    ensureMusicKit().then(function (MK) {
      return MK.configure({ developerToken: token, app: { name: "Disco Swipe", build: "1.0" } });
    }).then(function () {
      return MusicKit.getInstance().authorize();        // ユーザー認可（要サブスク）
    }).then(function () {
      state.appleConnected = true;
      updateAppleConnectUI();
      backfillApplePlaylist();                          // これまでキープした曲もまとめて追加
      var music = mkInstance();
      if (music) {                                      // 本編フル再生に切替(契約者)。失敗時はloadMKがプレビューへ戻す
        bindMKEvents(music);
        engine = "mk";
        toast("Apple Music連携：本編フル再生に切替");
        loadCurrent(state.started);
      } else {
        toast("Apple Musicと連携しました");
      }
    }).catch(function (err) {
      state.appleConnected = false;
      updateAppleConnectUI();
      toast("連携に失敗しました");
      if (window.console) console.warn("Apple Music connect error:", err);
    });
  }

  // MusicKitの再生状態をUIに同期。曲が終わったら自動スキップONなら次へ。
  var mkBound = false;
  function bindMKEvents(music) {
    if (mkBound || !music) return;
    mkBound = true;
    music.addEventListener("playbackStateDidChange", function () {
      if (!useMK()) return;
      setPlaying(!!music.isPlaying);
      var PS = window.MusicKit && MusicKit.PlaybackStates;
      if (PS && (music.playbackState === PS.completed || music.playbackState === PS.ended)) {
        if (state.autoSkip) softNext();               // 本編が終わったら次の曲へ(ONのとき)
        else setPlaying(false);
      }
    });
  }

  function appleHeaders() {
    var music = window.MusicKit && MusicKit.getInstance();
    return {
      "Authorization": "Bearer " + getAppleDevToken(),
      "Music-User-Token": music ? music.musicUserToken : "",
      "Content-Type": "application/json"
    };
  }

  function getOrCreateApplePlaylist() {
    if (state.applePlaylistId) return Promise.resolve(state.applePlaylistId);
    return fetch("https://api.music.apple.com/v1/me/library/playlists", {
      method: "POST", headers: appleHeaders(),
      body: JSON.stringify({ attributes: { name: "Disco Swipe", description: "Disco Swipeでキープした曲" } })
    }).then(function (r) { return r.json(); }).then(function (data) {
      var id = data && data.data && data.data[0] && data.data[0].id;
      if (id) { state.applePlaylistId = id; try { localStorage.setItem("discoSwipe.applePlaylistId", id); } catch (e) {} }
      return id;
    });
  }

  function addTrackToApplePlaylist(track) {
    if (!state.appleConnected || !track) return Promise.resolve();
    return getOrCreateApplePlaylist().then(function (pid) {
      if (!pid) return;
      return fetch("https://api.music.apple.com/v1/me/library/playlists/" + pid + "/tracks", {
        method: "POST", headers: appleHeaders(),
        body: JSON.stringify({ data: [{ id: String(track.id), type: "songs" }] })
      });
    }).catch(function (err) { if (window.console) console.warn("Apple Music add failed:", err); });
  }

  function backfillApplePlaylist() {
    (state.apple || []).slice().reverse().forEach(function (t) { addTrackToApplePlaylist(t); });
  }

  function updateAppleConnectUI() {
    if (!els.appleConnectBtn) return;
    if (state.appleConnected) {
      els.appleConnectBtn.textContent = "連携済み ✓ 本編フル再生";
      els.appleConnectBtn.classList.add("connected");
      els.appleConnectNote.textContent = "Apple Musicで本編をフル再生中。いいねした曲は「Disco Swipe」プレイリストに自動追加されます。";
    } else {
      els.appleConnectBtn.textContent = "Apple Musicと連携";
      els.appleConnectBtn.classList.remove("connected");
      els.appleConnectNote.textContent = "連携すると本編をフル再生でき、いいねした曲が Apple Music のプレイリストに自動追加されます。（要 Apple Music サブスク。未連携時は公式30秒プレビュー）";
    }
  }

  // いいね(左右スワイプ)時に呼ばれる。連携済みなら自動で実プレイリストへ、未連携ならローカル保存のみ。
  function addToAppleMusicPlaylist(track) {
    if (state.appleConnected) {
      addTrackToApplePlaylist(track);
    } else if (window.console) {
      console.info("[Apple Music] 未連携のためローカル保存のみ:", track.trackName, "—", track.artistName);
    }
  }

  function slim(t) {
    return {
      id: t.id, trackName: t.trackName, artistName: t.artistName,
      artwork: t.artworkSmall || t.artwork, trackViewUrl: t.trackViewUrl,
      bucket: t.bucket || bucketOf(t)         // おすすめ学習用にジャンル区分を保持
    };
  }
  function existsIn(arr, id) { for (var i = 0; i < arr.length; i++) if (arr[i].id === id) return true; return false; }

  function updateCounts() {
    els.libCount.textContent = state.fav.length;
    els.favCount.textContent = state.fav.length;
    els.appleCount.textContent = state.apple.length;
  }

  /* ---------- ライブラリパネル ---------- */
  function openLibrary() { renderLists(); els.libraryPanel.classList.remove("hidden"); }
  function closeLibrary() { els.libraryPanel.classList.add("hidden"); }

  /* ---------- 歌詞（無料の lyrics.ovh から取得。無ければ検索リンクにフォールバック） ---------- */
  function primaryArtist(name) { return (name || "").split(/,|&|feat\.|ft\.|with /i)[0].trim(); }
  function cleanTitle(name) {
    var c = (name || "").replace(/\(.*?\)|\[.*?\]|feat\..*$|ft\..*$/gi, "").trim();
    return c || (name || "");
  }
  function openLyrics() {
    var t = currentTrack(); if (!t) return;
    els.lyricsTitle.textContent = t.trackName;
    els.lyricsArtist.textContent = t.artistName;
    els.lyricsPanel.classList.remove("hidden");
    if (lyricsCache[t.id] !== undefined) { showLyrics(t, lyricsCache[t.id]); return; }
    els.lyricsBody.className = "lyrics-body loading";
    els.lyricsBody.textContent = "歌詞を取得中…";
    fetchLyrics(t).then(function (text) {
      lyricsCache[t.id] = text || null;
      showLyrics(t, lyricsCache[t.id]);
    });
  }
  function showLyrics(t, text) {
    els.lyricsBody.className = "lyrics-body";
    if (text) { els.lyricsBody.textContent = text; els.lyricsBody.scrollTop = 0; return; }
    els.lyricsBody.textContent = "";
    var p = document.createElement("p");
    p.className = "lyrics-empty";
    p.textContent = "この曲の歌詞は見つかりませんでした。（無料の歌詞データベースは洋楽中心のため、邦楽・K-POP・ボカロ等は見つからないことがあります）";
    var a = document.createElement("a");
    a.className = "lyrics-search"; a.target = "_blank"; a.rel = "noopener noreferrer";
    a.href = "https://www.google.com/search?q=" + encodeURIComponent(t.artistName + " " + t.trackName + " 歌詞");
    a.textContent = "歌詞をWebで検索";
    els.lyricsBody.appendChild(p);
    els.lyricsBody.appendChild(a);
  }
  function closeLyrics() { els.lyricsPanel.classList.add("hidden"); }
  function fetchLyrics(t) {
    var url = "https://api.lyrics.ovh/v1/" + encodeURIComponent(primaryArtist(t.artistName)) +
      "/" + encodeURIComponent(cleanTitle(t.trackName));
    // 5秒で諦めて検索リンクにフォールバック(APIが遅い/届かない時にUIを固めない)
    var ctrl = (typeof AbortController !== "undefined") ? new AbortController() : null;
    var timer = setTimeout(function () { if (ctrl) ctrl.abort(); }, 5000);
    return fetch(url, ctrl ? { signal: ctrl.signal } : undefined)
      .then(function (r) { clearTimeout(timer); return r.ok ? r.json() : null; })
      .then(function (d) { return (d && d.lyrics) ? d.lyrics.trim() : null; })
      .catch(function () { clearTimeout(timer); return null; });
  }

  function renderLists() {
    renderList(els.favList, state.fav, "まだいいねした曲はありません。左右スワイプでいいね！", removeFavorite);
    renderList(els.appleList, state.apple, "まだ追加はありません。", removeApple);
  }
  // いいね(お気に入り)から削除 — 間違えていいねした曲を後から取り消せる
  function removeFavorite(id) {
    state.fav = state.fav.filter(function (t) { return t.id !== id; });
    saveLS(LS_FAV, state.fav);
    updateCounts();
    renderLists();
  }
  function removeApple(id) {
    state.apple = state.apple.filter(function (t) { return t.id !== id; });
    saveLS(LS_APPLE, state.apple);
    updateCounts();
    renderLists();
  }
  function renderList(ul, arr, emptyMsg, onRemove) {
    ul.textContent = "";
    if (!arr.length) {
      var li = document.createElement("li");
      li.className = "lib-empty";
      li.textContent = emptyMsg;
      ul.appendChild(li);
      return;
    }
    var frag = document.createDocumentFragment();
    arr.forEach(function (t) {
      var li = document.createElement("li");
      var img = document.createElement("img");
      img.src = t.artwork || ""; img.alt = ""; img.loading = "lazy";
      var meta = document.createElement("div");
      meta.className = "lib-meta";
      var b = document.createElement("b"); b.textContent = t.trackName;
      var sp = document.createElement("span"); sp.textContent = t.artistName;
      meta.appendChild(b); meta.appendChild(sp);
      li.appendChild(img); li.appendChild(meta);
      if (t.trackViewUrl) {
        var a = document.createElement("a");
        a.className = "lib-open"; a.textContent = "開く";
        a.href = t.trackViewUrl; a.target = "_blank"; a.rel = "noopener noreferrer";
        li.appendChild(a);
      }
      if (onRemove) {                              // 削除(×)ボタン
        var del = document.createElement("button");
        del.className = "lib-del"; del.type = "button";
        del.setAttribute("aria-label", "削除"); del.textContent = "×";
        del.addEventListener("click", (function (id) { return function () { onRemove(id); }; })(t.id));
        li.appendChild(del);
      }
      frag.appendChild(li);
    });
    ul.appendChild(frag);
  }

  /* =========================================================
     UIバインド
     ========================================================= */
  function bindUI() {
    // スワイプはステージ上のみ(下部ボタンと干渉させない)
    els.stage.addEventListener("pointerdown", onDown);
    els.stage.addEventListener("pointermove", onMove);
    els.stage.addEventListener("pointerup", onUp);
    els.stage.addEventListener("pointercancel", onUp);

    els.prevBtn.addEventListener("click", goPrev);          // 一個前に戻る
    els.playBtn.addEventListener("click", togglePlay);        // 再生 / 停止
    els.nextBtn.addEventListener("click", goNext);           // 次の曲へ

    // ジャンルチップ
    var chips = els.genreBar.querySelectorAll(".chip");
    for (var c = 0; c < chips.length; c++) {
      chips[c].addEventListener("click", function () {
        selectBucket(this.getAttribute("data-bucket"));
      });
    }

    els.autoSkipBtn.addEventListener("click", toggleAutoSkip);
    els.libraryBtn.addEventListener("click", openLibrary);
    els.libraryClose.addEventListener("click", closeLibrary);
    els.libraryPanel.addEventListener("click", function (e) {
      if (e.target === els.libraryPanel) closeLibrary();
    });

    // 歌詞ボタンは廃止（パネル/取得関数は未使用のため残置）
    var tabs = document.querySelectorAll(".lib-tab");
    for (var i = 0; i < tabs.length; i++) {
      tabs[i].addEventListener("click", function () {
        for (var j = 0; j < tabs.length; j++) tabs[j].classList.toggle("is-active", tabs[j] === this);
        var tab = this.getAttribute("data-tab");
        els.favList.classList.toggle("hidden", tab !== "fav");
        els.appleSection.classList.toggle("hidden", tab !== "apple");
      });
    }
    els.appleConnectBtn.addEventListener("click", connectAppleMusic);

    els.startBtn.addEventListener("click", startApp);

    // PC/検証用キーボード操作
    window.addEventListener("keydown", function (e) {
      if (!state.started) return;
      if (e.key === "ArrowUp")   { e.preventDefault(); commit("next"); }
      else if (e.key === "ArrowDown") { e.preventDefault(); commit("prev"); }
      else if (e.key === "ArrowRight" || e.key === "ArrowLeft") likeCurrent();  // ←→=いいね(曲はそのまま)
      else if (e.key === " ") { e.preventDefault(); togglePlay(); }
    });
  }

  function startApp() {
    if (!state.tracks.length) return;
    state.started = true;
    els.startOverlay.classList.add("hidden");
    ensureAudioCtx();                          // スクラッチ音用のAudioContextもこの操作で解放
    if (actx && actx.state === "suspended") { try { actx.resume(); } catch (e) {} }
    loadAudio(currentTrack(), true);           // ユーザー操作内でplay()→iOSのオーディオ解放
  }

  /* =========================================================
     iOS Safari 対策まとめ
     ========================================================= */
  function guardIOS() {
    // ピンチズーム(ジェスチャ)抑止
    ["gesturestart", "gesturechange", "gestureend"].forEach(function (ev) {
      document.addEventListener(ev, function (e) { e.preventDefault(); }, { passive: false });
    });
    // 長押しの選択/コンテキストメニュー抑止(連打時の誤作動防止)
    document.addEventListener("contextmenu", function (e) { e.preventDefault(); });
    // セレクション開始抑止
    document.addEventListener("selectstart", function (e) { e.preventDefault(); });
  }

  /* ---------- ユーティリティ ---------- */
  function clamp(v, a, b) { return Math.max(a, Math.min(b, v)); }
  function shuffle(a) {
    for (var i = a.length - 1; i > 0; i--) {
      var j = Math.floor(Math.random() * (i + 1));
      var tmp = a[i]; a[i] = a[j]; a[j] = tmp;
    }
    return a;
  }
  // iOS Safari は Vibration API 非対応。<input switch>(iOS17.4+) のトグルでハプティクスを出す。
  var _hsw = null;
  function iosTick() {
    try {
      if (!_hsw) {
        var lb = document.createElement("label");
        lb.setAttribute("aria-hidden", "true");
        lb.style.cssText = "position:fixed;left:-9999px;top:0;width:1px;height:1px;";
        var ip = document.createElement("input");
        ip.type = "checkbox"; ip.setAttribute("switch", "");
        lb.appendChild(ip); document.body.appendChild(lb);
        _hsw = ip;
      }
      _hsw.click();                 // トグル → iOSがハプティクスを再生
    } catch (e) {}
  }
  function haptic() {
    if (navigator.vibrate) { try { navigator.vibrate(12); } catch (e) {} }  // Android等
    iosTick();                                                              // iOS
  }
  function haptic2x() {             // 2倍速用の強め(2連)フィードバック
    if (navigator.vibrate) { try { navigator.vibrate([22, 30, 22]); } catch (e) {} }
    iosTick(); setTimeout(iosTick, 80);
  }

  // 名前自体に区切り文字を含む「単独アクト」。コラボに誤判定しないよう、そのまま1組として扱う。
  // (例: King & Prince を "King" に切ってしまうとコラボ扱いになり、出現頻度が偏る)
  var ATOMIC_ARTISTS = {
    "king & prince": 1,
    "tyler, the creator": 1,
    "神様、僕は気づいてしまった": 1,
    "chico with honeyworks": 1,
    "selena gomez & the scene": 1
  };

  // 名義からリード(主役)アーティストを取り出す。"BTS & Megan"→"BTS"、"GLAY×EXILE"→"GLAY"。
  // これで総当たりがコラボ名義ごとに枠を取らず、アーティスト単位でまとまる。
  function leadArtist(name) {
    name = (name || "(?)").trim();
    if (ATOMIC_ARTISTS[name.toLowerCase()]) return name;   // 単独アクト(名前に記号を含む)はそのまま
    var delims = [" & ", " × ", "×", " feat", " ft.", " with ", " vs ", " x ", ", ", "、", "＆", "&"];
    var cut = name.length;
    for (var i = 0; i < delims.length; i++) {
      var p = name.indexOf(delims[i]);
      if (p > 0 && p < cut) cut = p;            // 先頭(&TEAM等)は切らない
    }
    return name.slice(0, cut).trim() || name;
  }
  // 名義を参加アーティストの配列に分解（"A, B & C feat. D" → [A,B,C,D]）
  function participantsOf(name) {
    name = (name || "").trim();
    var parts = name.split(/\s*(?:&|＆|×|,|、|\/|\bfeat\.?\b|\bft\.?\b|\bwith\b|\bvs\.?\b|\bx\b)\s*/i);
    var out = [];
    for (var i = 0; i < parts.length; i++) { var p = parts[i].trim(); if (p) out.push(p); }
    return out.length ? out : [name];
  }
  // 同じ参加アーティスト(客演含む)が gap 曲以内に再登場しないよう並べ替える。
  // コラボが多いジャンルで「同じ声が何度も出る」のを防いで“バラバラ”感を上げる。
  function spreadParticipants(order, gap) {
    var n = order.length;
    if (n < 4) return order;
    var parts = new Array(n);
    for (var i = 0; i < n; i++) parts[i] = participantsOf(order[i].artistName);
    var used = new Uint8Array(n), res = [], recent = [], recentSet = {};
    function addRecent(ps) {
      recent.push(ps);
      for (var x = 0; x < ps.length; x++) recentSet[ps[x]] = (recentSet[ps[x]] || 0) + 1;
      if (recent.length > gap) {
        var old = recent.shift();
        for (var y = 0; y < old.length; y++) if (--recentSet[old[y]] <= 0) delete recentSet[old[y]];
      }
    }
    for (var k = 0; k < n; k++) {
      var pick = -1;
      for (var j = 0; j < n; j++) {
        if (used[j]) continue;
        var clash = false;
        for (var q = 0; q < parts[j].length; q++) { if (recentSet[parts[j][q]]) { clash = true; break; } }
        if (!clash) { pick = j; break; }
      }
      if (pick < 0) { for (var m = 0; m < n; m++) if (!used[m]) { pick = m; break; } }
      used[pick] = 1; res.push(order[pick]); addRecent(parts[pick]);
    }
    return res;
  }
  var REMIX_RE = /remix|mix|リミックス|\bedit\b/i;
  // ソロ(単独アーティストが歌う・リミックスでない)曲か
  function isSolo(t) {
    var a = (t.artistName || "").trim();
    if (leadArtist(a) !== a) return false;      // 名義に複数アーティスト=コラボ
    return !REMIX_RE.test(t.trackName || "");   // リミックス/エディットでない
  }
  // ソロ曲を前に、コラボ/リミックスを後ろに(安定: 元の未聴優先順は保つ)
  function soloFirst(arr) {
    var solo = [], other = [];
    for (var i = 0; i < arr.length; i++) (isSolo(arr[i]) ? solo : other).push(arr[i]);
    return solo.concat(other);
  }
  // 約10曲に1曲、有名曲(hit)が来るように差し込む。obscureな曲ばかりで飽きるのを防ぐ。
  // hit曲を一旦抜き出し、約9曲ごとに1曲ずつ戻す(hitが尽きたら通常曲のみ続行)。
  function hitSpacing(order) {
    var hits = [], rest = [];
    for (var i = 0; i < order.length; i++) (order[i].hit ? hits : rest).push(order[i]);
    if (!hits.length || !rest.length) return order;
    var out = [], ri = 0, hi = 0, GAP = 9;        // 通常9曲ごとに有名曲1曲 → 約10曲に1曲
    while (ri < rest.length || hi < hits.length) {
      for (var c = 0; c < GAP && ri < rest.length; c++) out.push(rest[ri++]);
      if (hi < hits.length) out.push(hits[hi++]);
    }
    return out;
  }

  // 最終整形: ソロ曲を主役にしつつコラボ/リミックスも少しだけ混ぜる(ソロ:コラボ 最大4:1)。
  // ★コラボ枠を「全体に均等に薄く」散らすのが肝。固定の4:1で先頭に詰めると、コラボ枠が
  //   少ないとき(=周回が速い)に特定の名義(例: King & Prince のような記号入り単独アクトが
  //   コラボ誤判定された場合)がその枠を独占して偏る。gapをコラボ数に応じて広げて防ぐ。
  function soloBias(order) {
    var solo = [], other = [];
    for (var i = 0; i < order.length; i++) (isSolo(order[i]) ? solo : other).push(order[i]);
    if (!solo.length || !other.length) return order;
    // ソロgap曲ごとにコラボ1曲。コラボが少ないほどgapを広げ、全体に均等分散させる(最低でも4:1)。
    var gap = Math.max(4, Math.floor(solo.length / other.length));
    var out = [], si = 0, oi = 0;
    while (si < solo.length || oi < other.length) {
      for (var c = 0; c < gap && si < solo.length; c++) out.push(solo[si++]);
      if (oi < other.length) out.push(other[oi++]);
    }
    return out;
  }

  var toastTimer;
  function toast(msg) {
    els.toast.textContent = msg;
    els.toast.classList.add("show");
    clearTimeout(toastTimer);
    toastTimer = setTimeout(function () { els.toast.classList.remove("show"); }, 1400);
  }
  function setStatus(s) { if (els.startStatus) els.startStatus.textContent = s; }

  function loadLS(k) { try { return JSON.parse(localStorage.getItem(k)) || []; } catch (e) { return []; } }
  function saveLS(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch (e) {} }

  /* ---------- 縦向き維持: 横向きにしても回転で縦画面を保つ(表示は一切出さない) ----------
     端末の自動回転をキャンセルするため、OSが回した角度ぶんだけ逆回転させて
     常にポートレート(縦)のフレームに固定する。左回し/右回しの両方に対応。 */
  function keepPortrait() {
    var w = window.innerWidth, h = window.innerHeight;
    var landscape = w > h && h <= 600;                  // スマホを横にした状態だけ対象
    var cls = document.body.classList;
    cls.remove("lock-cw", "lock-ccw");
    if (!landscape) return;
    var ang = (window.screen && screen.orientation && typeof screen.orientation.angle === "number")
      ? screen.orientation.angle
      : (typeof window.orientation === "number" ? (window.orientation + 360) % 360 : 90);
    // OSの回転(ang)を打ち消す向きに回す: ang=90 →逆時計(-90), それ以外(270)→時計(+90)
    cls.add(ang === 90 ? "lock-ccw" : "lock-cw");
  }
  window.addEventListener("resize", keepPortrait);
  window.addEventListener("orientationchange", keepPortrait);
  keepPortrait();

})();
